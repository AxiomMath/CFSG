module

public import Mathlib.GroupTheory.Sylow

public section

open MulAction

namespace CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs

theorem dvd_card_of_orbit_dvd {K Ω : Type*} [Group K] [MulAction K Ω] [Finite K] [Finite Ω]
    (d : ℕ) (h : ∀ ω : Ω, d ∣ Nat.card (orbit K ω)) : d ∣ Nat.card Ω := by
  classical
  have := Fintype.ofFinite Ω
  have key : Nat.card Ω = ∑ q : orbitRel.Quotient K Ω, Nat.card (orbit K q.out) := by
    rw [Nat.card_congr (selfEquivSigmaOrbits K Ω), Nat.card_sigma]
  rw [key]
  exact Finset.dvd_sum fun q _ => h q.out

theorem exists_orbit_card_eq_of_not_dvd {K Ω : Type*} [Group K] [MulAction K Ω] [Finite K]
    [Finite Ω] {p : ℕ} [hp : Fact p.Prime] (hK : IsPGroup p K) (v : ℕ)
    (hdiv : ∀ ω : Ω, p ^ v ∣ Nat.card (orbit K ω))
    (hnd : ¬ p ^ (v + 1) ∣ Nat.card Ω) :
    ∃ ω : Ω, Nat.card (orbit K ω) = p ^ v := by
  by_contra hne
  have hne' : ∀ ω : Ω, Nat.card (orbit K ω) ≠ p ^ v := fun ω h => hne ⟨ω, h⟩
  apply hnd
  refine dvd_card_of_orbit_dvd (K := K) _ ?_
  intro ω
  obtain ⟨u, hu⟩ := IsPGroup.card_orbit hK ω
  have hvu : v ≤ u := by
    have h := hdiv ω
    rw [hu] at h
    exact (Nat.pow_dvd_pow_iff_le_right hp.out.one_lt).1 h
  have hne2 : u ≠ v := by
    intro huv
    exact hne' ω (by rw [hu, huv])
  rw [hu]
  exact Nat.pow_dvd_pow p (by omega)

theorem map_stabilizer_subtype_eq {H Ω : Type*} [Group H] [MulAction H Ω] (P : Subgroup H)
    (ω : Ω) :
    (stabilizer P ω).map P.subtype = stabilizer H ω ⊓ P := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, y.2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨x, h2⟩, h1, rfl⟩

theorem card_orbit_mul_card_stabilizer_inf {H Ω : Type*} [Group H] [MulAction H Ω] [Finite H]
    (P : Subgroup H) (ω : Ω) :
    Nat.card (orbit P ω) * Nat.card (stabilizer H ω ⊓ P : Subgroup H) = Nat.card P := by
  have h1 := Subgroup.card_mul_index (stabilizer P ω)
  have h2 := MulAction.index_stabilizer P ω
  have h3 : Nat.card (stabilizer P ω) = Nat.card (stabilizer H ω ⊓ P : Subgroup H) := by
    rw [← map_stabilizer_subtype_eq]
    exact (Subgroup.card_map_of_injective (f := P.subtype) Subtype.val_injective).symm
  have h4 : Nat.card (orbit P ω) = (orbit P ω).ncard := Nat.card_coe_set_eq _
  rw [h4, ← h2, ← h3, mul_comm]
  exact h1

theorem pow_dvd_card_orbit_of_le {H Ω : Type*} [Group H] [MulAction H Ω] [Finite H] [Finite Ω]
    {p : ℕ} [hp : Fact p.Prime] (T P : Subgroup H) (hPT : P ≤ T)
    (hT : ∀ ω : Ω, Nat.card Ω * Nat.card (stabilizer H ω ⊓ T : Subgroup H) = Nat.card T)
    (hPc : ∃ c : ℕ, Nat.card P = p ^ c)
    (hP : ∀ m : ℕ, p ^ m ∣ Nat.card T → p ^ m ∣ Nat.card P)
    (v : ℕ) (hv : p ^ v ∣ Nat.card Ω) (ω : Ω) :
    p ^ v ∣ Nat.card (orbit P ω) := by
  obtain ⟨c, hc⟩ := hPc
  have e1 := card_orbit_mul_card_stabilizer_inf P ω
  have hSU : Nat.card (stabilizer H ω ⊓ P : Subgroup H) ∣
      Nat.card (stabilizer H ω ⊓ T : Subgroup H) :=
    Subgroup.card_dvd_of_le (inf_le_inf_left _ hPT)
  have hSP : Nat.card (stabilizer H ω ⊓ P : Subgroup H) ∣ p ^ c := by
    rw [← hc]
    exact Subgroup.card_dvd_of_le inf_le_right
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow hp.out).1 hSP
  have hdiv : p ^ (v + a) ∣ Nat.card T := by
    rw [← hT ω, pow_add, ← ha]
    exact mul_dvd_mul hv hSU
  have hdivP : p ^ (v + a) ∣ Nat.card P := hP _ hdiv
  rw [← e1, ha, pow_add] at hdivP
  exact Nat.dvd_of_mul_dvd_mul_right (pow_pos hp.out.pos a) hdivP

section Factor

variable {H : Type*} [Group H] [Finite H]

omit [Finite H] in
theorem smul_base_eq_iff (B : Subgroup H) (h : H) :
    h • (QuotientGroup.mk (1 : H) : H ⧸ B) = QuotientGroup.mk 1 ↔ h ∈ B := by
  rw [show h • (QuotientGroup.mk (1 : H) : H ⧸ B) = QuotientGroup.mk (h * 1) from rfl,
    QuotientGroup.eq]
  simp

omit [Finite H] in
theorem exists_smul_base_eq {A B : Subgroup H} (hfac : ∀ h : H, ∃ a ∈ A, ∃ b ∈ B, h = a * b)
    (y : H ⧸ B) : ∃ a ∈ A, a • (QuotientGroup.mk (1 : H) : H ⧸ B) = y := by
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨a, ha, b, hb, rfl⟩ := hfac v
  refine ⟨a, ha, ?_⟩
  show QuotientGroup.mk (a * 1) = QuotientGroup.mk (a * b)
  rw [QuotientGroup.eq]
  simpa using hb

omit [Finite H] in
theorem orbit_eq_univ_of_factor {A B : Subgroup H} (hfac : ∀ h : H, ∃ a ∈ A, ∃ b ∈ B, h = a * b)
    (ω : H ⧸ B) : orbit A ω = Set.univ := by
  ext η
  simp only [Set.mem_univ, iff_true]
  obtain ⟨a₁, ha₁, h₁⟩ := exists_smul_base_eq hfac ω
  obtain ⟨a₂, ha₂, h₂⟩ := exists_smul_base_eq hfac η
  rw [mem_orbit_iff]
  refine ⟨⟨a₂ * a₁⁻¹, A.mul_mem ha₂ (A.inv_mem ha₁)⟩, ?_⟩
  change (a₂ * a₁⁻¹ : H) • ω = η
  rw [← h₁, ← h₂, smul_smul, inv_mul_cancel_right]

theorem card_mul_card_stab_inf_A {A B : Subgroup H}
    (hfac : ∀ h : H, ∃ a ∈ A, ∃ b ∈ B, h = a * b) (ω : H ⧸ B) :
    Nat.card (H ⧸ B) * Nat.card (stabilizer H ω ⊓ A : Subgroup H) = Nat.card A := by
  have := card_orbit_mul_card_stabilizer_inf A ω
  rw [orbit_eq_univ_of_factor hfac, Nat.card_univ] at this
  exact this

end Factor

section Conj

variable {H Ω : Type*} [Group H] [MulAction H Ω]

theorem orbit_map_conj_eq (P : Subgroup H) (g : H) (ω : Ω) :
    orbit (P.map (MulAut.conj g).toMonoidHom : Subgroup H) (g • ω) =
      (fun x => g • x) '' orbit P ω := by
  ext x
  constructor
  · rintro ⟨⟨y, hy⟩, rfl⟩
    obtain ⟨h, hh, hy'⟩ := Subgroup.mem_map.1 hy
    refine ⟨h • ω, ⟨⟨h, hh⟩, rfl⟩, ?_⟩
    have hy'' : y = g * h * g⁻¹ := hy'.symm
    subst hy''
    show g • (h • ω) = (g * h * g⁻¹) • (g • ω)
    simp [smul_smul, mul_assoc]
  · rintro ⟨z, ⟨⟨h, hh⟩, rfl⟩, rfl⟩
    refine ⟨⟨g * h * g⁻¹, Subgroup.mem_map.2 ⟨h, hh, ?_⟩⟩, ?_⟩
    · simp [MulAut.conj_apply]
    · show (g * h * g⁻¹) • (g • ω) = g • (h • ω)
      simp [smul_smul, mul_assoc]

theorem card_orbit_map_conj (P : Subgroup H) (g : H) (ω : Ω) :
    Nat.card (orbit (P.map (MulAut.conj g).toMonoidHom : Subgroup H) (g • ω)) =
      Nat.card (orbit P ω) := by
  rw [orbit_map_conj_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq,
    Set.ncard_image_of_injective _ (MulAction.injective g)]

end Conj

section Core

variable {H : Type*} [Group H] [Finite H]

theorem pow_dvd_of_card_eq {p N n m : ℕ} (hp : p.Prime) (hN : N ≠ 0)
    (hn : n = p ^ N.factorization p) (hm : p ^ m ∣ N) : p ^ m ∣ n := by
  rw [hn]
  exact pow_dvd_pow p ((Nat.Prime.pow_dvd_iff_le_factorization hp hN).1 hm)

theorem not_dvd_index_of_card {p : ℕ} [Fact p.Prime] (K : Subgroup H)
    (hK : Nat.card K = p ^ (Nat.card H).factorization p) : ¬ p ∣ K.index := by
  intro hdiv
  have hH : Nat.card H ≠ 0 := (Nat.card_pos (α := H)).ne'
  have hmul : Nat.card K * K.index = Nat.card H := Subgroup.card_mul_index K
  have key : p ^ ((Nat.card H).factorization p + 1) ∣ Nat.card K * K.index := by
    rw [hK, pow_succ]
    exact mul_dvd_mul_left _ hdiv
  rw [hmul] at key
  exact Nat.pow_succ_factorization_not_dvd hH Fact.out key

theorem exists_sylow_factor_core {p : ℕ} [Fact p.Prime] {A B : Subgroup H}
    (hfac : ∀ h : H, ∃ a ∈ A, ∃ b ∈ B, h = a * b) :
    ∃ P : Subgroup H, IsPGroup p P ∧ ¬ p ∣ P.index ∧
      ∀ w ∈ P, ∃ a ∈ P ⊓ A, ∃ b ∈ P ⊓ B, w = a * b := by
  classical
  have hΩpos : 0 < Nat.card (H ⧸ B) := Nat.card_pos
  have hA0 : Nat.card A ≠ 0 := (Nat.card_pos (α := A)).ne'
  have hH0 : Nat.card H ≠ 0 := (Nat.card_pos (α := H)).ne'
  have hv : p ^ (Nat.card (H ⧸ B)).factorization p ∣ Nat.card (H ⧸ B) :=
    Nat.ordProj_dvd _ p
  have hnd : ¬ p ^ ((Nat.card (H ⧸ B)).factorization p + 1) ∣ Nat.card (H ⧸ B) :=
    Nat.pow_succ_factorization_not_dvd hΩpos.ne' Fact.out
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := A) p
    (n := (Nat.card A).factorization p) (Nat.ordProj_dvd _ p)
  set Q : Subgroup H := K.map A.subtype with hQdef
  have hQcard : Nat.card Q = p ^ (Nat.card A).factorization p := by
    rw [hQdef, Subgroup.card_map_of_injective Subtype.val_injective]
    exact hK
  have hQA : Q ≤ A := by
    rintro _ ⟨x, _, rfl⟩
    exact x.2
  have hQp : IsPGroup p Q := IsPGroup.of_card hQcard
  obtain ⟨P₀s, hQP₀⟩ := IsPGroup.exists_le_sylow hQp
  set P₀ : Subgroup H := (P₀s : Subgroup H) with hP₀def
  have hP₀card : Nat.card P₀ = p ^ (Nat.card H).factorization p :=
    Sylow.card_eq_multiplicity P₀s
  have hP₀p : IsPGroup p P₀ := IsPGroup.of_card hP₀card
  have hfacTop : ∀ h : H, ∃ a ∈ (⊤ : Subgroup H), ∃ b ∈ B, h = a * b :=
    fun h => ⟨h, Subgroup.mem_top h, 1, B.one_mem, (mul_one h).symm⟩
  have hP₀dvd : ∀ m : ℕ, p ^ m ∣ Nat.card (⊤ : Subgroup H) → p ^ m ∣ Nat.card P₀ := by
    intro m hm
    rw [Subgroup.card_top] at hm
    exact pow_dvd_of_card_eq Fact.out hH0 hP₀card hm
  obtain ⟨ω₁, hω₁⟩ := exists_orbit_card_eq_of_not_dvd (K := P₀) (Ω := H ⧸ B) hP₀p
    ((Nat.card (H ⧸ B)).factorization p)
    (fun ω => pow_dvd_card_orbit_of_le (⊤ : Subgroup H) P₀ le_top
      (fun ω' => card_mul_card_stab_inf_A hfacTop ω') ⟨_, hP₀card⟩ hP₀dvd _ hv ω)
    hnd
  obtain ⟨a, ha, haω⟩ := exists_smul_base_eq (A := A) (B := B) hfac ω₁
  have hconj : a⁻¹ • ω₁ = (QuotientGroup.mk (1 : H) : H ⧸ B) := by
    rw [← haω, inv_smul_smul]
  set P : Subgroup H := P₀.map (MulAut.conj a⁻¹).toMonoidHom with hPdef
  set Q' : Subgroup H := Q.map (MulAut.conj a⁻¹).toMonoidHom with hQ'def
  have hconjinj : Function.Injective (MulAut.conj a⁻¹).toMonoidHom :=
    (MulAut.conj a⁻¹).injective
  have hPcard : Nat.card P = p ^ (Nat.card H).factorization p := by
    rw [hPdef, Subgroup.card_map_of_injective hconjinj]
    exact hP₀card
  have hPp : IsPGroup p P := IsPGroup.of_card hPcard
  have hPidx : ¬ p ∣ P.index := not_dvd_index_of_card P hPcard
  have hPorb : Nat.card (orbit P (QuotientGroup.mk (1 : H) : H ⧸ B)) =
      p ^ (Nat.card (H ⧸ B)).factorization p := by
    have h := card_orbit_map_conj P₀ a⁻¹ ω₁
    rw [hconj] at h
    exact h.trans hω₁
  have hQ'P : Q' ≤ P := Subgroup.map_mono hQP₀
  have hQ'A : Q' ≤ A := by
    rintro _ ⟨x, hx, rfl⟩
    show a⁻¹ * x * (a⁻¹)⁻¹ ∈ A
    rw [inv_inv]
    exact A.mul_mem (A.mul_mem (A.inv_mem ha) (hQA hx)) ha
  have hQ'card : Nat.card Q' = p ^ (Nat.card A).factorization p := by
    rw [hQ'def, Subgroup.card_map_of_injective hconjinj]
    exact hQcard
  have hdivQ : p ^ (Nat.card (H ⧸ B)).factorization p ∣
      Nat.card (orbit Q' (QuotientGroup.mk (1 : H) : H ⧸ B)) :=
    pow_dvd_card_orbit_of_le A Q' hQ'A (fun ω' => card_mul_card_stab_inf_A hfac ω') ⟨_, hQ'card⟩
      (fun m hm => pow_dvd_of_card_eq Fact.out hA0 hQ'card hm) _ hv _
  have hsub : orbit Q' (QuotientGroup.mk (1 : H) : H ⧸ B) ⊆
      orbit P (QuotientGroup.mk (1 : H) : H ⧸ B) := by
    rintro _ ⟨⟨q, hq⟩, rfl⟩
    exact ⟨⟨q, hQ'P hq⟩, rfl⟩
  have hpos : 0 < Nat.card (orbit Q' (QuotientGroup.mk (1 : H) : H ⧸ B)) := by
    have : Nonempty (orbit Q' (QuotientGroup.mk (1 : H) : H ⧸ B)) :=
      ⟨⟨_, MulAction.mem_orbit_self _⟩⟩
    exact Nat.card_pos
  have hle : (orbit P (QuotientGroup.mk (1 : H) : H ⧸ B)).ncard ≤
      (orbit Q' (QuotientGroup.mk (1 : H) : H ⧸ B)).ncard := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hPorb]
    exact Nat.le_of_dvd hpos hdivQ
  have heq := Set.eq_of_subset_of_ncard_le hsub hle
  refine ⟨P, hPp, hPidx, ?_⟩
  intro w hwP
  have hw : w • (QuotientGroup.mk (1 : H) : H ⧸ B) ∈
      orbit P (QuotientGroup.mk (1 : H) : H ⧸ B) := ⟨⟨w, hwP⟩, rfl⟩
  rw [← heq] at hw
  obtain ⟨⟨q, hq⟩, hqw⟩ := hw
  have hqw' : q • (QuotientGroup.mk (1 : H) : H ⧸ B) = w • (QuotientGroup.mk (1 : H) : H ⧸ B) := hqw
  have hqP : q ∈ P := hQ'P hq
  have hbB : q⁻¹ * w ∈ B := by
    rw [← smul_base_eq_iff B]
    rw [mul_smul, ← hqw', inv_smul_smul]
  refine ⟨q, ⟨hqP, hQ'A hq⟩, q⁻¹ * w, ⟨P.mul_mem (P.inv_mem hqP) hwP, hbB⟩, ?_⟩
  exact (mul_inv_cancel_left q w).symm

end Core

section Final

theorem exists_sylow_eq_mul_of_mul {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {M A B : Subgroup G} (hAM : A ≤ M) (hBM : B ≤ M)
    (hfac : ∀ m ∈ M, ∃ a ∈ A, ∃ b ∈ B, m = a * b) :
    ∃ W : Subgroup G, W ≤ M ∧ IsPGroup p W ∧ ¬ p ∣ (W.subgroupOf M).index ∧
      ∀ w ∈ W, ∃ a ∈ W ⊓ A, ∃ b ∈ W ⊓ B, w = a * b := by
  classical
  have hfacM : ∀ h : M, ∃ a ∈ A.subgroupOf M, ∃ b ∈ B.subgroupOf M, h = a * b := by
    intro h
    obtain ⟨a, ha, b, hb, hab⟩ := hfac h.1 h.2
    exact ⟨⟨a, hAM ha⟩, Subgroup.mem_subgroupOf.2 ha, ⟨b, hBM hb⟩,
      Subgroup.mem_subgroupOf.2 hb, Subtype.ext hab⟩
  obtain ⟨P, hPp, hPidx, hPfac⟩ := exists_sylow_factor_core (p := p) hfacM
  refine ⟨P.map M.subtype, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, _, rfl⟩
    exact x.2
  · obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hPp
    exact IsPGroup.of_card (n := n)
      (by rw [Subgroup.card_map_of_injective Subtype.val_injective]; exact hn)
  · have hWP : (P.map M.subtype).subgroupOf M = P := by
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
      constructor
      · rintro ⟨y, hy, hyx⟩
        have : y = x := Subtype.ext hyx
        exact this ▸ hy
      · intro hx
        exact ⟨x, hx, rfl⟩
    rw [hWP]
    exact hPidx
  · rintro w ⟨y, hy, rfl⟩
    obtain ⟨a, ha, b, hb, hab⟩ := hPfac y hy
    refine ⟨a.1, Subgroup.mem_inf.2 ⟨Subgroup.mem_map.2 ⟨a, (Subgroup.mem_inf.1 ha).1, rfl⟩,
      Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 ha).2⟩,
      b.1, Subgroup.mem_inf.2 ⟨Subgroup.mem_map.2 ⟨b, (Subgroup.mem_inf.1 hb).1, rfl⟩,
      Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 hb).2⟩, ?_⟩
    rw [hab]
    rfl

end Final

end CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs

end
