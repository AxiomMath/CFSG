module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma116
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma129

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129e

open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf autBar barAut innerAut)
open CFSG.HardMathSupport.Solomon.UniquenessMaximal (centralizer_barX_eq card_barX_of_isPGroup elemAbelian_barX)

theorem three_pow_ge (u : ℕ) : 2 * u + 1 ≤ 3 ^ u := by
  induction u with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    omega

theorem arith_big {p r t n : ℕ} (hp : 3 ≤ p) (hr : 2 ≤ r) (ht1 : 1 ≤ t) (ht : t < r)
    (hn : p ^ r ≤ n) : r + 1 ≤ t * (n / p ^ t) := by
  obtain ⟨u, rfl⟩ : ∃ u, r = t + u := ⟨r - t, by omega⟩
  have hu : 1 ≤ u := by omega
  have h1 : p ^ u ≤ n / p ^ t := by
    rw [Nat.le_div_iff_mul_le (pow_pos (by omega) _)]
    calc p ^ u * p ^ t = p ^ (t + u) := by rw [← pow_add, add_comm]
      _ ≤ n := hn
  have h2 : 3 ^ u ≤ p ^ u := Nat.pow_le_pow_left hp u
  have h3 := three_pow_ge u
  calc t + u + 1 ≤ t * (2 * u + 1) := by nlinarith
    _ ≤ t * (n / p ^ t) := Nat.mul_le_mul_left _ (by omega)

theorem arith_strict {r t n : ℕ} (hr : 2 ≤ r) (ht1 : 1 ≤ t) (ht : t < r)
    (hn : 3 ^ r + 4 ≤ n) : r + 2 ≤ t * (n / 3 ^ t) := by
  obtain ⟨u, rfl⟩ : ∃ u, r = t + u := ⟨r - t, by omega⟩
  have hu : 1 ≤ u := by omega
  have h3 := three_pow_ge u
  by_cases ht2 : t = 1
  · subst ht2
    have h1 : 3 ^ u + 1 ≤ n / 3 ^ 1 := by
      rw [Nat.le_div_iff_mul_le (by norm_num)]
      calc (3 ^ u + 1) * 3 ^ 1 = 3 ^ (1 + u) + 3 := by rw [add_mul, ← pow_add, add_comm u 1]; ring
        _ ≤ n := by omega
    calc 1 + u + 2 ≤ 3 ^ u + 1 := by omega
      _ ≤ 1 * (n / 3 ^ 1) := by omega
  · have ht2' : 2 ≤ t := by omega
    have h1 : 3 ^ u ≤ n / 3 ^ t := by
      rw [Nat.le_div_iff_mul_le (pow_pos (by norm_num) _)]
      calc 3 ^ u * 3 ^ t = 3 ^ (t + u) := by rw [← pow_add, add_comm]
        _ ≤ n := by omega
    calc t + u + 2 ≤ t * (2 * u + 1) := by nlinarith
      _ ≤ t * (n / 3 ^ t) := Nat.mul_le_mul_left _ (by omega)

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

@[expose] noncomputable def orbitLen {K : Type*} [Group K] {n : ℕ} (φ : K ≃* alternatingGroup (Fin n))
    (B : Subgroup K) (i : Fin n) : ℕ :=
  Set.ncard {j : Fin n | ∃ b ∈ B, ((φ b : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) i = j}

@[expose] def Input23_5 : Prop :=
  ∀ (p n k : ℕ), p.Prime → p ≠ 2 → ¬ p ∣ n → 1 ≤ k → p ^ (k + 1) < n →
    ∀ (K : Type) [Group K] [Finite K] (φ : K ≃* alternatingGroup (Fin n)) (B : Subgroup K),
      B ≠ ⊥ → IsElemAbelian p B → (∀ i, orbitLen φ B i ≤ p ^ k) → (∃ i, orbitLen φ B i = p ^ k) →
      ∃ E : Subgroup K, IsElemAbelian p E ∧ (∀ x ∈ B, ∀ y ∈ E, x * y = y * x) ∧
        k * (n / p ^ k) ≤ CFSG.Open.pRank p E ∧ GLBCore p 2 E = ⊤

section Orbit

variable {K : Type*} [Group K] {n : ℕ}

theorem orbitLen_pow {p : ℕ} (hp : p.Prime) [Finite K] (φ : K ≃* alternatingGroup (Fin n))
    {B : Subgroup K} (hB : IsPGroup p B) (i : Fin n) : ∃ j : ℕ, orbitLen φ B i = p ^ j := by
  haveI : Fact p.Prime := ⟨hp⟩
  let ρ : ↥B →* Equiv.Perm (Fin n) :=
    ((alternatingGroup (Fin n)).subtype.comp φ.toMonoidHom).comp B.subtype
  letI : MulAction ↥B (Fin n) := MulAction.compHom (Fin n) ρ
  have hset : {j : Fin n | ∃ b ∈ B, ((φ b : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) i = j} =
      MulAction.orbit ↥B i := by
    ext j
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨⟨b, hb⟩, rfl⟩
    · rintro ⟨⟨b, hb⟩, rfl⟩
      exact ⟨b, hb, rfl⟩
  have h1 : (MulAction.orbit ↥B i).ncard ∣ Nat.card B := by
    rw [← MulAction.index_stabilizer ↥B i]
    exact ⟨_, (Subgroup.index_mul_card _).symm⟩
  obtain ⟨k, hk⟩ := hB.exists_card_eq
  rw [hk] at h1
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 h1
  refine ⟨j, ?_⟩
  unfold orbitLen
  rw [hset]
  exact hj

theorem orbitLen_le_card [Finite K] (φ : K ≃* alternatingGroup (Fin n)) (B : Subgroup K)
    (i : Fin n) : orbitLen φ B i ≤ Nat.card B := by
  unfold orbitLen
  have hfin : (B : Set K).Finite := Set.toFinite _
  have : {j : Fin n | ∃ b ∈ B, ((φ b : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) i = j} =
      (fun b : K => ((φ b : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) i) '' (B : Set K) := by
    ext j
    simp
  rw [this]
  calc _ ≤ (B : Set K).ncard := Set.ncard_image_le hfin
    _ = Nat.card B := (Nat.card_coe_set_eq (B : Set K)).symm

theorem exists_orbit_exponent {p : ℕ} (hp : p.Prime) [Finite K] (φ : K ≃* alternatingGroup (Fin n))
    {B : Subgroup K} (hB : IsPGroup p B) (hB1 : B ≠ ⊥) :
    ∃ t : ℕ, 1 ≤ t ∧ (∀ i, orbitLen φ B i ≤ p ^ t) ∧ ∃ i, orbitLen φ B i = p ^ t := by
  have hn : Nonempty (Fin n) := by
    by_contra hne
    apply hB1
    rw [eq_bot_iff]
    intro b _
    have : ((φ b : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) = 1 := by
      ext i
      exact absurd ⟨i⟩ hne
    have h2 : φ b = 1 := Subtype.ext this
    rw [Subgroup.mem_bot]
    exact φ.injective (by rw [h2, map_one])
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n))
    (fun i => orbitLen φ B i) (Finset.univ_nonempty_iff.2 hn)
  obtain ⟨t, ht⟩ := orbitLen_pow hp φ hB i₀
  refine ⟨t, ?_, fun i => ?_, ⟨i₀, ht⟩⟩
  · by_contra ht1
    have ht0 : t = 0 := by omega
    apply hB1
    rw [eq_bot_iff]
    intro b hb
    have hall : ∀ i : Fin n, ((φ b : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) i = i := by
      intro i
      have hle := hi₀ i (Finset.mem_univ i)
      rw [ht, ht0, pow_zero] at hle
      have h1 : orbitLen φ B i = 1 := by
        have : 0 < orbitLen φ B i := by
          unfold orbitLen
          apply Set.ncard_pos (Set.toFinite _) |>.2
          exact ⟨i, 1, B.one_mem, by simp⟩
        omega
      unfold orbitLen at h1
      obtain ⟨c, hc⟩ := Set.ncard_eq_one.1 h1
      have hi : i ∈ ({c} : Set (Fin n)) := by
        rw [← hc]
        exact ⟨1, B.one_mem, by simp⟩
      have hbi : ((φ b : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) i ∈ ({c} : Set (Fin n)) := by
        rw [← hc]
        exact ⟨b, hb, rfl⟩
      rw [Set.mem_singleton_iff] at hi hbi
      exact hbi.trans hi.symm
    have h2 : φ b = 1 := Subtype.ext (Equiv.ext hall)
    rw [Subgroup.mem_bot]
    exact φ.injective (by rw [h2, map_one])
  · have := hi₀ i (Finset.mem_univ i)
    rw [ht] at this
    exact this

end Orbit

section Acl

variable {Y : Type} [Group Y] [Finite Y]

theorem acl_perm (h23 : Input23_5) {p n t : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpn : ¬ p ∣ n)
    (ht1 : 1 ≤ t) (htn : p ^ (t + 1) < n) {K₀ H : Subgroup Y}
    (ψ : K₀ ≃* alternatingGroup (Fin n)) (κ : ↥H →* ↥K₀)
    (hκ : ∀ (a : ↥H) (x : ↥K₀), ((a : H) : Y) * (x : Y) * ((a : H) : Y)⁻¹ =
      ((κ a : K₀) : Y) * (x : Y) * ((κ a : K₀) : Y)⁻¹)
    (hH : IsElemAbelian p H) (hB : κ.range ≠ ⊥)
    (horb1 : ∀ i, orbitLen ψ κ.range i ≤ p ^ t) (horb2 : ∃ i, orbitLen ψ κ.range i = p ^ t) :
    ∃ P : Subgroup Y, P ≤ K₀ ∧ IsElemAbelian p P ∧ (∀ x ∈ H, ∀ y ∈ P, x * y = y * x) ∧
      t * (n / p ^ t) ≤ CFSG.Open.pRank p P ∧ K₀ ≤ GLBCore p 2 P := by
  have hBel : IsElemAbelian p κ.range := by
    have hFtop : IsElemAbelian p (⊤ : Subgroup ↥H) := by
      have := hH.subgroupOf H
      rwa [Subgroup.subgroupOf_self] at this
    rw [MonoidHom.range_eq_map]
    exact hFtop.map κ
  obtain ⟨E, hEel, hBE, hrank, hcore⟩ := h23 p n t hp hp2 hpn ht1 htn ↥K₀ ψ κ.range hB hBel
    horb1 horb2
  refine ⟨E.map K₀.subtype, ?_, hEel.map _, ?_, ?_, ?_⟩
  · rintro _ ⟨e, -, rfl⟩
    exact e.2
  · rintro x hx _ ⟨e, he, rfl⟩
    have h1 := hκ ⟨x, hx⟩ e
    have h2 := hBE (κ ⟨x, hx⟩) ⟨⟨x, hx⟩, rfl⟩ e he
    have h3 : (κ ⟨x, hx⟩ : ↥K₀) * e = e * κ ⟨x, hx⟩ := h2
    have h4 := congrArg Subtype.val h3
    simp only [Subgroup.coe_mul] at h4
    simp only [Subgroup.coe_subtype]
    have h1' : x * (e : Y) * x⁻¹ = ((κ ⟨x, hx⟩ : K₀) : Y) * (e : Y) * ((κ ⟨x, hx⟩ : K₀) : Y)⁻¹ := h1
    calc x * (e : Y) = (x * (e : Y) * x⁻¹) * x := by group
      _ = (((κ ⟨x, hx⟩ : K₀) : Y) * (e : Y) * ((κ ⟨x, hx⟩ : K₀) : Y)⁻¹) * x := by rw [h1']
      _ = (e : Y) * x := by rw [h4]; group
  · rw [pRank_map_eq_of_injective hp.one_lt K₀.subtype K₀.subtype_injective]
    exact hrank
  · intro k hk
    have hk' : (⟨k, hk⟩ : ↥K₀) ∈ GLBCore p 2 E := by rw [hcore]; exact Subgroup.mem_top _
    have hle : GLBCore p 2 E ≤ (GLBCore p 2 (E.map K₀.subtype)).comap K₀.subtype := by
      refine sSup_le ?_
      rintro _ ⟨Q, hQE, hQ2, rfl⟩
      intro g hg
      show (g : Y) ∈ GLBCore p 2 (E.map K₀.subtype)
      have hQ' : Q.map K₀.subtype ≤ E.map K₀.subtype := Subgroup.map_mono hQE
      have hrk : 2 ≤ CFSG.Open.pRank p (Q.map K₀.subtype) := by
        rw [pRank_map_eq_of_injective hp.one_lt K₀.subtype K₀.subtype_injective]
        exact hQ2
      have hmem : Subgroup.normalizer ((Q.map K₀.subtype : Subgroup Y) : Set Y) ≤
          GLBCore p 2 (E.map K₀.subtype) :=
        le_sSup ⟨Q.map K₀.subtype, hQ', hrk, rfl⟩
      apply hmem
      rw [Subgroup.mem_normalizer_iff] at hg ⊢
      intro y
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact ⟨g * q * g⁻¹, (hg q).1 hq, rfl⟩
      · rintro ⟨q', hq', hy⟩
        have hq'' : g⁻¹ * q' * g ∈ Q := by
          refine (hg (g⁻¹ * q' * g)).2 ?_
          have : g * (g⁻¹ * q' * g) * g⁻¹ = q' := by group
          rw [this]; exact hq'
        refine ⟨g⁻¹ * q' * g, hq'', ?_⟩
        simp only [Subgroup.coe_subtype, Subgroup.coe_mul, InvMemClass.coe_inv]
        have hy' : (q' : Y) = (g : Y) * y * (g : Y)⁻¹ := hy
        calc (g : Y)⁻¹ * (q' : Y) * (g : Y) = (g : Y)⁻¹ * ((g : Y) * y * (g : Y)⁻¹) * (g : Y) := by
              rw [hy']
          _ = y := by group
    exact hle hk'

end Acl

section AclG

variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A N D : Subgroup G}

theorem glbCore_barX_le_barX_M (h : Cex127 G m p B M E A N D) {P : Subgroup G} (hPN : P ≤ N)
    (hPel : IsElemAbelian p P) (hPc : ∀ x ∈ E ⊓ A, ∀ y ∈ P, x * y = y * x)
    (hrank : CFSG.Open.pRank p A < CFSG.Open.pRank p ((E ⊓ A) ⊔ P)) :
    GLBCore p 2 (barX p N P) ≤ barX p N M := by
  have hp := prime_of h
  have hA0el : IsElemAbelian p (E ⊓ A) := (A_el h).mono inf_le_right
  have hWel : IsElemAbelian p ((E ⊓ A) ⊔ P) := hA0el.sup_of_commute hPel hPc
  refine sSup_le ?_
  rintro _ ⟨Q, hQP, hQ2, rfl⟩
  obtain ⟨E', hE'P, hE'Q, hE'r⟩ := exists_le_barX_eq hp hPel.isPGroup hPN hQP
  have hE'N : E' ≤ N := hE'P.trans hPN
  rw [← hE'Q]
  refine (normalizer_barX_le hp (hPel.isPGroup.to_le hE'P) hE'N).trans (barX_mono129 ?_)
  have hrank2 : 2 ≤ CFSG.Open.pRank p E' := by rw [hE'r]; exact hQ2
  exact normalizer_le_of_rank_gt h hWel le_sup_left hrank (hE'P.trans le_sup_right) hrank2

theorem acl_cover (h23 : Input23_5) (h : Cex127 G m p B M E A N D)
    {K₀ : Subgroup (↥N ⧸ GLAPPrimeCore p ↥N)} {n t : ℕ} (hpn : ¬ p ∣ n) (ht1 : 1 ≤ t)
    (htn : p ^ (t + 1) < n) (ψ : ↥K₀ ≃* alternatingGroup (Fin n))
    (κ : ↥(barX p N (E ⊓ A)) →* ↥K₀)
    (hκ : ∀ (a : ↥(barX p N (E ⊓ A))) (x : ↥K₀),
      ((a : barX p N (E ⊓ A)) : ↥N ⧸ GLAPPrimeCore p ↥N) * (x : ↥N ⧸ GLAPPrimeCore p ↥N) *
        ((a : barX p N (E ⊓ A)) : ↥N ⧸ GLAPPrimeCore p ↥N)⁻¹ =
      ((κ a : K₀) : ↥N ⧸ GLAPPrimeCore p ↥N) * (x : ↥N ⧸ GLAPPrimeCore p ↥N) *
        ((κ a : K₀) : ↥N ⧸ GLAPPrimeCore p ↥N)⁻¹)
    (hB : κ.range ≠ ⊥) (horb1 : ∀ i, orbitLen ψ κ.range i ≤ p ^ t)
    (horb2 : ∃ i, orbitLen ψ κ.range i = p ^ t) :
    ∃ P : Subgroup G, P ≤ N ∧ IsElemAbelian p P ∧ (∀ x ∈ E ⊓ A, ∀ y ∈ P, x * y = y * x) ∧
      t * (n / p ^ t) ≤ CFSG.Open.pRank p P ∧ barX p N P ≤ K₀ ∧
      (CFSG.Open.pRank p A < CFSG.Open.pRank p ((E ⊓ A) ⊔ P) → K₀ ≤ barX p N M) := by
  have hp := prime_of h
  have hp2 := ne_two_of h
  have hAN := A_le_N h
  have hA0N : E ⊓ A ≤ N := inf_le_right.trans hAN
  have hA0el : IsElemAbelian p (E ⊓ A) := (A_el h).mono inf_le_right
  obtain ⟨Pb, hPbK, hPbel, hPbc, hrank, hcore⟩ := acl_perm h23 hp hp2 hpn ht1 htn ψ κ hκ
    (isElemAbelian_barX hA0el) hB horb1 horb2
  have hPbcent : Pb ≤ Subgroup.centralizer ((barX p N (E ⊓ A) : Subgroup (↥N ⧸ GLAPPrimeCore p ↥N)) :
      Set (↥N ⧸ GLAPPrimeCore p ↥N)) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hPbc x hx y hy
  rw [centralizer_barX_eq hp hA0N hA0el.isPGroup] at hPbcent
  obtain ⟨P, hPle, hPp, hPbar⟩ := Lemma116.exists_lift hp
    (inf_le_left : N ⊓ Subgroup.centralizer ((E ⊓ A : Subgroup G) : Set G) ≤ N) hPbcent
    hPbel.isPGroup
  have hPN : P ≤ N := hPle.trans inf_le_left
  have hPc : P ≤ Subgroup.centralizer ((E ⊓ A : Subgroup G) : Set G) := hPle.trans inf_le_right
  have hPel : IsElemAbelian p P :=
    Lemma116.elemAbelian_of_barX_elemAbelian hp hPN hPp (hPbar ▸ hPbel)
  have hPcomm : ∀ x ∈ E ⊓ A, ∀ y ∈ P, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.1 (hPc hy) x hx
  have hPrank : CFSG.Open.pRank p Pb = CFSG.Open.pRank p P := by
    have h1 := card_barX_of_isPGroup hp hPN hPp
    rw [hPbar, card_eq_pow_pRank hp hPbel, card_eq_pow_pRank hp hPel] at h1
    exact (Nat.pow_right_injective hp.two_le) h1
  refine ⟨P, hPN, hPel, hPcomm, hPrank ▸ hrank, hPbar ▸ hPbK, fun hr => ?_⟩
  have hgen := glbCore_barX_le_barX_M h hPN hPel hPcomm hr
  rw [hPbar] at hgen
  exact hcore.trans hgen

end AclG

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129e

end
