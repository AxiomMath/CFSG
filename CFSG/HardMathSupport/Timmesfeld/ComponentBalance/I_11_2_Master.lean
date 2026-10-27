module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_StructZ
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_FamilyRank
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_StructAct

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

section Generic

variable {G : Type*} [Group G] [Finite G] {p : ℕ}

theorem rank_combine (hp : p.Prime) {T F C W : Subgroup G} (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T)
    (hF : IsElemAbelian p F) (hC : IsElemAbelian p C)
    (hcomm : ∀ a ∈ F, ∀ b ∈ C, a * b = b * a) (hW : F ⊓ C ≤ W) {c : ℕ}
    (hWc : CFSG.Open.pRank p W ≤ c) (hN : F ⊔ C ≤ Subgroup.normalizer (T : Set G))
    {f b : ℕ} (hf : Nat.card F = p ^ f) (hb : Nat.card C = p ^ b) :
    f + b ≤ GLATwoLocalRank p G + c := by
  obtain ⟨hFC, hcard⟩ := card_mul_le_card_sup_mul_pow hp hF hC hcomm hW hWc
  obtain ⟨k, hk⟩ := isElemAbelian_exists_card_eq_pow hp hFC
  have hkle : k ≤ GLATwoLocalRank p G :=
    le_glaTwoLocalRank_of_le_normalizer hp.one_lt hT hT2 hFC hN hk
  rw [hf, hb, hk, ← pow_add, ← pow_add] at hcard
  have := (Nat.pow_le_pow_iff_right hp.one_lt).1 hcard
  omega

end Generic

section Aux

theorem sum_ite_add {ι : Type*} [Fintype ι] [DecidableEq ι] (k₀ : ι) (w m : ℕ) :
    (∑ k, if k = k₀ then w else m) + m = w + Fintype.card ι * m := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k₀)]
  have h1 : ∑ k ∈ Finset.univ.erase k₀, (if k = k₀ then w else m) =
      ∑ k ∈ Finset.univ.erase k₀, m :=
    Finset.sum_congr rfl fun k hk => by simp [Finset.ne_of_mem_erase hk]
  have h0 : (if k₀ = k₀ then w else m) = w := by simp
  rw [h1, h0, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ k₀),
    smul_eq_mul, Finset.card_univ]
  have hpos : 0 < Fintype.card ι := Fintype.card_pos_iff.2 ⟨k₀⟩
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card ι = n + 1 := ⟨Fintype.card ι - 1, by omega⟩
  rw [hn]
  simp only [Nat.add_sub_cancel]
  ring

end Aux

section Main

variable {X : Type} [Group X] [Finite X] {p : ℕ} {B L : Subgroup X}

theorem pRank_centreIn_eq_center (hp : 1 < p) (L : Subgroup X) :
    CFSG.Open.pRank p (centreIn L) = CFSG.Open.pRank p (Subgroup.center ↥L) := by
  rw [← map_subtype_center L]
  exact pRank_map_eq_of_injective hp L.subtype L.subtype_injective _

omit [Finite X] in
theorem centreIn_gLBConj (g : X) (M : Subgroup X) :
    centreIn (GLBConj g M) = GLBConj g (centreIn M) := by
  ext x
  simp only [mem_centreIn, mem_gLBConj]
  constructor
  · rintro ⟨hx, hc⟩
    refine ⟨hx, fun h hh => ?_⟩
    have hy : g * (g⁻¹ * h * g) * g⁻¹ ∈ M := by
      simpa [mul_assoc] using hh
    have := hc _ hy
    calc h * (g * x * g⁻¹) = g * ((g⁻¹ * h * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * h * g)) * g⁻¹ := by rw [this]
      _ = g * x * g⁻¹ * h := by group
  · rintro ⟨hx, hc⟩
    refine ⟨hx, fun y hy => ?_⟩
    have := hc _ hy
    calc y * x = g⁻¹ * ((g * y * g⁻¹) * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * (g * y * g⁻¹)) * g := by rw [this]
      _ = x * y := by group

theorem pRank_centreIn_orbit (hp : 1 < p) {M : Subgroup X} (hM : M ∈ i112Orbit B L) :
    CFSG.Open.pRank p (centreIn M) = CFSG.Open.pRank p (Subgroup.center ↥L) := by
  obtain ⟨g, -, rfl⟩ := mem_i112Orbit.1 hM
  rw [centreIn_gLBConj, pRank_gLBConj hp, pRank_centreIn_eq_center hp]

theorem pRank_orbit_eq_top (hp : 1 < p) {M : Subgroup X} (hM : M ∈ i112Orbit B L) :
    CFSG.Open.pRank p M = CFSG.Open.pRank p (⊤ : Subgroup ↥L) := by
  obtain ⟨g, -, rfl⟩ := mem_i112Orbit.1 hM
  rw [pRank_gLBConj hp, pRank_eq_pRank_top_subtype hp]

theorem i112_master (hp : p.Prime) (hO : GLAPPrimeCore p X = ⊥) (hB : IsElemAbelian p B)
    (hr : GLATwoLocalRank p X ≤ CFSG.Open.pRank p B) (hL : GLAPComponent p ⊤ L)
    (hnL : ¬ B ≤ Subgroup.normalizer (L : Set X)) (h2 : ∃ t : ↥L, orderOf t = 2) :
    ∃ r a : ℕ, 1 ≤ r ∧ (Subgroup.normalizer (L : Set X)).relIndex B = p ^ r ∧
      Nat.card (i112H B L) = p ^ a ∧ CFSG.Open.pRank p (i112H B L) = a ∧
      CFSG.Open.pRank p (i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X)) +
        GLATwoLocalRank p ↥L + p ^ r * CFSG.Open.pRank p (⊤ : Subgroup ↥L) ≤
      r + a + CFSG.Open.pRank p ((i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X)) ⊓ B) +
        p ^ r * CFSG.Open.pRank p (Subgroup.center ↥L) + CFSG.Open.pRank p (⊤ : Subgroup ↥L) := by
  classical
  have : Fintype ↥(i112Orbit B L) := Fintype.ofFinite _
  have hp1 := hp.one_lt
  have hLc : IsComponentOf L ⊤ := i116pI_isComponentOf hO hL
  obtain ⟨r, a, hr1, hrel, hHa, hHr, hBrank⟩ := i112_pRank_formula hp hB hnL
  refine ⟨r, a, hr1, hrel, hHa, hHr, ?_⟩
  obtain ⟨T, E₁, hTL, hE₁L, hT, hT2, hE₁a, hE₁N, hE₁c⟩ :=
    exists_twoLocal_attaining_subgroup hp1 L h2
  obtain ⟨E₀, hE₀Z, hE₀a, hE₀c⟩ := CFSG.SectionRank.exists_pRank hp1
    (i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X))
  have hex : ∀ k : ↥(i112Orbit B L), ∃ E : Subgroup X, E ≤ (k : Subgroup X) ∧
      IsElemAbelian p E ∧ Nat.card E = p ^ CFSG.Open.pRank p (⊤ : Subgroup ↥L) := fun k => by
    obtain ⟨E, hE, ha, hc⟩ := CFSG.SectionRank.exists_pRank hp1 (k : Subgroup X)
    exact ⟨E, hE, ha, by rw [hc, pRank_orbit_eq_top hp1 k.2]⟩
  choose E' hE'L hE'a hE'c using hex
  let k₀ : ↥(i112Orbit B L) := ⟨L, i112_self_mem_orbit⟩
  let E : ↥(i112Orbit B L) → Subgroup X := fun k => if k = k₀ then E₁ else E' k
  let e : ↥(i112Orbit B L) → ℕ := fun k =>
    if k = k₀ then GLATwoLocalRank p ↥L else CFSG.Open.pRank p (⊤ : Subgroup ↥L)
  have hEL : ∀ k, E k ≤ i112Fam B L k := by
    intro k
    by_cases hk : k = k₀
    · simp only [E, hk, ↓reduceIte]
      exact hE₁L
    · simp only [E, hk, ↓reduceIte]
      exact hE'L k
  have hEa : ∀ k, IsElemAbelian p (E k) := by
    intro k
    by_cases hk : k = k₀
    · simp only [E, hk, ↓reduceIte]
      exact hE₁a
    · simp only [E, hk, ↓reduceIte]
      exact hE'a k
  have hEc : ∀ k, Nat.card (E k) = p ^ e k := by
    intro k
    by_cases hk : k = k₀
    · simp only [E, e, hk, ↓reduceIte]
      exact hE₁c
    · simp only [E, e, hk, ↓reduceIte]
      exact hE'c k
  have hcomm : CommFam (i112Fam B L) := i112_commFam hLc
  have hz : ∀ k, CFSG.Open.pRank p (centreIn (i112Fam B L k)) ≤
      CFSG.Open.pRank p (Subgroup.center ↥L) := fun k =>
    (pRank_centreIn_orbit hp1 k.2).le
  have hE₀cent : E₀ ≤ Subgroup.centralizer ((⨆ i, i112Fam B L i : Subgroup X) : Set X) := by
    rw [i112_iSup_fam]
    exact hE₀Z.trans inf_le_right
  obtain ⟨F, hFle, hFa, f, hf, hfle⟩ := hcomm.exists_elemAbelian_rank_le hp hz hE₀cent hE₀a E hEL
    hEa hE₀c hEc
  have hJcent_T : Subgroup.centralizer (i112J B L : Set X) ≤ Subgroup.centralizer (T : Set X) :=
    Subgroup.centralizer_le (fun x hx =>
      i112_orbit_le_J (M := L) i112_self_mem_orbit (hTL hx))
  have hFJ : F ≤ i112J B L := by
    refine hFle.trans (sup_le (hE₀Z.trans inf_le_left) (iSup_le fun k => ?_))
    exact (hEL k).trans (i112_orbit_le_J k.2)
  have hFN : F ≤ Subgroup.normalizer (T : Set X) := by
    refine hFle.trans (sup_le ?_ (iSup_le fun k => ?_))
    · exact (hE₀Z.trans inf_le_right).trans
        (hJcent_T.trans (Subgroup.centralizer_le_normalizer _))
    · by_cases hk : k = k₀
      · simp only [E, hk, ↓reduceIte]
        exact hE₁N
      · simp only [E, hk, ↓reduceIte]
        refine (hE'L k).trans ?_
        have hkk : (k : Subgroup X) ≤ Subgroup.centralizer (L : Set X) :=
          hcomm.le_centralizer (i := k₀) hk
        exact hkk.trans ((Subgroup.centralizer_le hTL).trans
          (Subgroup.centralizer_le_normalizer _))
  have hBc : IsElemAbelian p (i112Bc B L) := isElemAbelian_of_le hB i112Bc_le_B
  obtain ⟨b, hb⟩ := exists_card_eq_of_isElemAbelian hp hBc
  have hBcJ : i112Bc B L ≤ Subgroup.centralizer (i112J B L : Set X) := inf_le_right
  have hcomm' : ∀ x ∈ F, ∀ y ∈ i112Bc B L, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.1 (hBcJ hy) x (hFJ hx)
  have hW : F ⊓ i112Bc B L ≤
      (i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X)) ⊓ B := by
    intro x hx
    obtain ⟨hxF, hxC⟩ := Subgroup.mem_inf.1 hx
    exact Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hFJ hxF, hBcJ hxC⟩, i112Bc_le_B hxC⟩
  have hN : F ⊔ i112Bc B L ≤ Subgroup.normalizer (T : Set X) :=
    sup_le hFN (hBcJ.trans (hJcent_T.trans (Subgroup.centralizer_le_normalizer _)))
  have hcomb := rank_combine hp hT hT2 hFa hBc hcomm' hW le_rfl hN hf hb
  have hbrank : CFSG.Open.pRank p (i112Bc B L) = b := pRank_eq_of_card hp1 hBc hb
  have hsum := sum_ite_add k₀ (GLATwoLocalRank p ↥L) (CFSG.Open.pRank p (⊤ : Subgroup ↥L))
  have hcard : Fintype.card ↥(i112Orbit B L) = p ^ r := by
    rw [← Nat.card_eq_fintype_card, i112_natCard_orbit, hrel]
  rw [hcard] at hfle hsum
  have hsum' : ∑ k, e k + CFSG.Open.pRank p (⊤ : Subgroup ↥L) =
      GLATwoLocalRank p ↥L + p ^ r * CFSG.Open.pRank p (⊤ : Subgroup ↥L) := hsum
  omega

end Main

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance
