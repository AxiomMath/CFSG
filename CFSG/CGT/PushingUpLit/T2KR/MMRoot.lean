module

public import CFSG.CGT.PushingUpLit.T2KR.MMAct

public section

namespace CFSG.CGT.PushingUpLit.T2KR

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.T2K CFSG.CGT.PushingUpLit.BHS
  CFSG.QuasithinUnique.Setup.Campbell CFSG.QuasithinUnique.Setup.Offender
open scoped commutatorElement LinearAlgebra.Projectivization

section SL2

variable {F : Type} [Field F] [Finite F]

theorem exists_rootGrp_le {f : ℕ} (hf : Nat.card F = 2 ^ f)
    {X : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)} (hX : ∀ x ∈ X, x * x = 1) :
    ∃ p : ℙ F (Fin 2 → F), X ≤ rootGrp p := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXp : IsPGroup 2 X := fun x => ⟨1, by
    apply Subtype.ext
    simpa [pow_two] using hX x x.2⟩
  obtain ⟨P, hXP⟩ := hXp.exists_le_sylow
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hf1 : f ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hf
    omega
  have hP : Nat.card P.toSubgroup = Nat.card F := by
    rw [P.card_eq_multiplicity, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hf]
    have h1 : 2 ∣ (2 ^ f) ^ 2 := dvd_pow (dvd_pow_self 2 hf1) two_ne_zero
    have h2 : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    have h4 : 4 ≤ (2 ^ f) ^ 2 := by
      have : 2 ≤ 2 ^ f := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.2 hf1)
      nlinarith
    have hodd : ¬ 2 ∣ (2 ^ f) ^ 2 - 1 := by omega
    have hne : (2 ^ f) ^ 2 - 1 ≠ 0 := by omega
    rw [Nat.factorization_mul (by positivity) hne, Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd hodd, add_zero]
  obtain ⟨p, hp⟩ := exists_point_eq_rootGrp Nat.prime_two hf (P := P.toSubgroup) hP
  exact ⟨p, hXP.trans hp.le⟩

end SL2

variable {G : Type} [Group G] [Finite G]

namespace MData

variable {L M : Subgroup G} {n : ℕ} (H : MData G L M n)

include H in
theorem LQ_le : L ⊔ QM L M ≤ M := sup_le H.le inf_le_left

include H in
theorem actHom_mem_range {x : ↥M} (hx : (x : G) ∈ L ⊔ QM L M) :
    H.actHom x ∈ (slPerm (Fq n)).range := by
  obtain ⟨l, hl, q, hq, hlq⟩ := H.mem_LQ_iff.1 hx
  have hx' : x = ⟨l, H.le hl⟩ * ⟨q, hq.1⟩ := Subtype.ext hlq.symm
  refine ⟨H.D.φ ⟨l, hl⟩, ?_⟩
  rw [hx', map_mul, H.actHom_L ⟨l, hl⟩, (H.actHom_eq_one_iff _).2 hq.2, mul_one]

@[expose] noncomputable def rhoFun (x : ↥(L ⊔ QM L M)) : Matrix.SpecialLinearGroup (Fin 2) (Fq n) :=
  Classical.choose (H.actHom_mem_range (x := ⟨x, H.LQ_le x.2⟩) x.2)

theorem slPerm_rhoFun (x : ↥(L ⊔ QM L M)) :
    slPerm (Fq n) (H.rhoFun x) = H.actHom ⟨x, H.LQ_le x.2⟩ :=
  Classical.choose_spec (H.actHom_mem_range (x := ⟨x, H.LQ_le x.2⟩) x.2)

@[expose] noncomputable def rho :
    ↥(L ⊔ QM L M) →* Matrix.SpecialLinearGroup (Fin 2) (Fq n) where
  toFun := H.rhoFun
  map_one' := by
    apply slPerm_injective
    rw [H.slPerm_rhoFun, map_one]
    exact (map_one H.actHom : _)
  map_mul' x y := by
    apply slPerm_injective
    rw [map_mul, H.slPerm_rhoFun, H.slPerm_rhoFun, H.slPerm_rhoFun, ← map_mul]
    rfl

theorem slPerm_rho (x : ↥(L ⊔ QM L M)) :
    slPerm (Fq n) (H.rho x) = H.actHom ⟨x, H.LQ_le x.2⟩ := H.slPerm_rhoFun x

theorem rho_of_mem_L {l : G} (hl : l ∈ L) :
    H.rho ⟨l, (le_sup_left : L ≤ L ⊔ QM L M) hl⟩ = H.D.φ ⟨l, hl⟩ :=
  slPerm_injective (by rw [H.slPerm_rho]; exact H.actHom_L ⟨l, hl⟩)

theorem rho_of_mem_Q {q : G} (hq : q ∈ QM L M) :
    H.rho ⟨q, (le_sup_right : QM L M ≤ L ⊔ QM L M) hq⟩ = 1 :=
  slPerm_injective (by
    rw [H.slPerm_rho, map_one]
    exact (H.actHom_eq_one_iff _).2 hq.2)

theorem rho_eq_one_iff (x : ↥(L ⊔ QM L M)) : H.rho x = 1 ↔ (x : G) ∈ QM L M := by
  constructor
  · intro h
    have h1 : H.actHom ⟨x, H.LQ_le x.2⟩ = 1 := by rw [← H.slPerm_rho, h, map_one]
    exact ⟨H.LQ_le x.2, (H.actHom_eq_one_iff _).1 h1⟩
  · intro hx
    exact H.rho_of_mem_Q hx

theorem actHom_eq_smul (x : ↥(L ⊔ QM L M)) (w : Fin 2 → Fq n) :
    H.actHom ⟨x, H.LQ_le x.2⟩ w = H.rho x • w := by
  rw [← H.slPerm_rho x]
  rfl

theorem rho_surj_L (g : Matrix.SpecialLinearGroup (Fin 2) (Fq n)) :
    ∃ (l : G) (hl : l ∈ L), H.rho ⟨l, (le_sup_left : L ≤ L ⊔ QM L M) hl⟩ = g := by
  obtain ⟨l, hl⟩ := H.D.φ_surj g
  exact ⟨l, l.2, by rw [H.rho_of_mem_L l.2]; exact hl⟩

theorem twist_rho (x₀ : Matrix.SpecialLinearGroup (Fin 2) (Fq n)) (x : ↥(L ⊔ QM L M)) :
    (H.twist x₀).rho x = x₀⁻¹ * H.rho x * x₀ := by
  apply slPerm_injective
  rw [(H.twist x₀).slPerm_rho, H.twist_actHom, map_mul, map_mul, H.slPerm_rho]

@[expose] noncomputable def rhoOn (X : Subgroup G) (hX : X ≤ L ⊔ QM L M) :
    ↥X →* Matrix.SpecialLinearGroup (Fin 2) (Fq n) :=
  H.rho.comp (Subgroup.inclusion hX)

theorem rhoOn_apply (X : Subgroup G) (hX : X ≤ L ⊔ QM L M) (x : ↥X) :
    H.rhoOn X hX x = H.rho ⟨x, hX x.2⟩ := rfl

theorem rhoOn_ker (X : Subgroup G) (hX : X ≤ L ⊔ QM L M) :
    (H.rhoOn X hX).ker = (X ⊓ QM L M).subgroupOf X := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, rhoOn_apply, H.rho_eq_one_iff]
  exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩

theorem relIndex_eq_card_range (X : Subgroup G) (hX : X ≤ L ⊔ QM L M) :
    (X ⊓ QM L M).relIndex X = Nat.card (H.rhoOn X hX).range := by
  rw [Subgroup.relIndex, ← H.rhoOn_ker, Subgroup.index_ker]

include H in
theorem exists_root_point (X : Subgroup G) (hX : X ≤ L ⊔ QM L M) (hX2 : ∀ x ∈ X, x * x = 1) :
    ∃ p : ℙ (Fq n) (Fin 2 → Fq n), (H.rhoOn X hX).range ≤ rootGrp p := by
  have hn : n ≠ 0 := by have := H.nat.two_le; omega
  refine exists_rootGrp_le (f := n) (GaloisField.card 2 n hn) ?_
  rintro _ ⟨x, rfl⟩
  rw [← map_mul]
  have : x * x = 1 := Subtype.ext (hX2 x x.2)
  rw [this, map_one]

include H in
theorem relIndex_le_card (X : Subgroup G) (hX : X ≤ L ⊔ QM L M) (hX2 : ∀ x ∈ X, x * x = 1) :
    (X ⊓ QM L M).relIndex X ≤ Nat.card (Fq n) := by
  obtain ⟨p, hp⟩ := H.exists_root_point X hX hX2
  rw [H.relIndex_eq_card_range X hX]
  calc Nat.card (H.rhoOn X hX).range ≤ Nat.card (rootGrp p) := Subgroup.card_le_of_le hp
    _ = Nat.card (Fq n) := card_rootGrp p

theorem fixed_iff {p : ℙ (Fq n) (Fin 2 → Fq n)} {x : ↥(L ⊔ QM L M)} (hx : H.rho x ∈ rootGrp p)
    (hx1 : H.rho x ≠ 1) (w : Fin 2 → Fq n) :
    H.actHom ⟨x, H.LQ_le x.2⟩ w = w ↔ w ∈ p.submodule := by
  rw [H.actHom_eq_smul]
  exact smul_eq_self_iff_mem_of_mem_rootGrp hx hx1 w

theorem mem_centralizer_iff_fixed {X : Subgroup G} (hXM : X ≤ M) {v : G} (hv : v ∈ blockU L) :
    v ∈ Subgroup.centralizer (X : Set G) ↔
      ∀ x (hx : x ∈ X), H.actHom ⟨x, hXM hx⟩ (H.D.ψe v) = H.D.ψe v := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h x hx
    rw [H.actHom_apply, H.act_vec _ hv]
    congr 1
    have := h x hx
    calc (x : G) * v * (x : G)⁻¹ = (v * x) * (x : G)⁻¹ := by rw [← this]
      _ = v := by group
  · intro h x hx
    have h1 := h x hx
    rw [H.actHom_apply, H.act_vec _ hv] at h1
    have h2 : (x : G) * v * (x : G)⁻¹ = v :=
      H.ψe_injOn (conj_mem_blockU (H.normal (hXM hx)) hv) hv h1
    calc (x : G) * v = ((x : G) * v * (x : G)⁻¹) * x := by group
      _ = v * x := by rw [h2]

include H in
theorem card_CV (X : Subgroup G) (hXM : X ≤ M) :
    Nat.card ↥(blockU L ⊓ Subgroup.centralizer (X : Set G)) =
      Nat.card {w : Fin 2 → Fq n // ∀ x (hx : x ∈ X), H.actHom ⟨x, hXM hx⟩ w = w} := by
  refine Nat.card_congr (Equiv.ofBijective
    (fun v => ⟨H.D.ψe v.1, (H.mem_centralizer_iff_fixed hXM v.2.1).1 v.2.2⟩) ⟨?_, ?_⟩)
  · intro a b hab
    apply Subtype.ext
    exact H.ψe_injOn a.2.1 b.2.1 (congrArg Subtype.val hab)
  · rintro ⟨w, hw⟩
    refine ⟨⟨H.vec w, H.vec_mem w, ?_⟩, ?_⟩
    · exact (H.mem_centralizer_iff_fixed hXM (H.vec_mem w)).2 (by rw [H.ψe_vec]; exact hw)
    · apply Subtype.ext
      exact H.ψe_vec w

include H in
theorem commutator_mem {x : G} (hx : x ∈ L ⊔ QM L M) (hx2 : x * x = 1) {u : G}
    (hu : u ∈ QM L M) :
    u⁻¹ * (x * u * x⁻¹) ∈ blockU L ∧
      x * (u⁻¹ * (x * u * x⁻¹)) * x⁻¹ = u⁻¹ * (x * u * x⁻¹) := by
  have hmem : u⁻¹ * (x * u * x⁻¹) ∈ blockU L := by
    obtain ⟨l, hl, q, hq, rfl⟩ := H.mem_LQ_iff.1 hx
    have hqu : q * u = u * q := H.Q_comm q hq u hu
    have e : u⁻¹ * (l * q * u * (l * q)⁻¹) = delta u l := by
      have h1 : q * u * q⁻¹ = u := by rw [hqu]; group
      calc u⁻¹ * (l * q * u * (l * q)⁻¹) = u⁻¹ * (l * (q * u * q⁻¹) * l⁻¹) := by group
        _ = delta u l := by rw [h1]; simp only [delta]; group
    rw [e]
    exact H.nat.delta_mem H.normal hu hl
  refine ⟨hmem, ?_⟩
  have hv2 : (u⁻¹ * (x * u * x⁻¹)) * (u⁻¹ * (x * u * x⁻¹)) = 1 := by
    have := H.nat.sq_eq_one_of_mem_blockU hmem
    rwa [pow_two] at this
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have h1 : x * (u⁻¹ * (x * u * x⁻¹)) * x⁻¹ = (u⁻¹ * (x * u * x⁻¹))⁻¹ := by
    have e1 : x * (u⁻¹ * (x * u * x⁻¹)) * x⁻¹ = x * u⁻¹ * x * u * (x⁻¹ * x⁻¹) := by group
    have e2 : (u⁻¹ * (x * u * x⁻¹))⁻¹ = x * u⁻¹ * x⁻¹ * u := by group
    rw [e1, e2, hxi]
    have : x * x = 1 := hx2
    rw [this, mul_one]
  rw [h1]
  exact inv_eq_of_mul_eq_one_right hv2

theorem actHom_eq_one_of_rho {x : ↥(L ⊔ QM L M)} (h : H.rho x = 1) :
    H.actHom ⟨x, H.LQ_le x.2⟩ = 1 := by
  rw [← H.slPerm_rho x, h, map_one]

include H in
theorem commutator_mem_CV (X : Subgroup G) (hX : X ≤ L ⊔ QM L M) (hX2 : ∀ x ∈ X, x * x = 1)
    {u : G} (hu : u ∈ QM L M) {x : G} (hxX : x ∈ X) :
    u⁻¹ * (x * u * x⁻¹) ∈ blockU L ⊓ Subgroup.centralizer (X : Set G) := by
  obtain ⟨p, hp⟩ := H.exists_root_point X hX hX2
  obtain ⟨hv, hvx⟩ := H.commutator_mem (hX hxX) (hX2 x hxX) hu
  have hXM : X ≤ M := hX.trans (H.LQ_le)
  refine ⟨hv, (H.mem_centralizer_iff_fixed hXM hv).2 ?_⟩
  have hρ : ∀ y (hy : y ∈ X), H.rho ⟨y, hX hy⟩ ∈ rootGrp p := fun y hy =>
    hp ⟨⟨y, hy⟩, rfl⟩
  by_cases hx1 : H.rho ⟨x, hX hxX⟩ = 1
  ·
    have hxQ : x ∈ QM L M := (H.rho_eq_one_iff ⟨x, hX hxX⟩).1 hx1
    have : u⁻¹ * (x * u * x⁻¹) = 1 := by
      rw [H.Q_comm x hxQ u hu]
      group
    intro y hy
    rw [this, H.D.ψe_one]
    exact (H.isSemilinear_sigma ⟨y, hXM hy⟩).map_zero
  · have hmem : H.D.ψe (u⁻¹ * (x * u * x⁻¹)) ∈ p.submodule := by
      refine (H.fixed_iff (hρ x hxX) hx1 _).1 ?_
      rw [H.actHom_apply, H.act_vec _ hv, hvx]
    intro y hy
    by_cases hy1 : H.rho ⟨y, hX hy⟩ = 1
    · have : H.actHom ⟨y, hXM hy⟩ = 1 := H.actHom_eq_one_of_rho hy1
      rw [this]
      rfl
    · exact (H.fixed_iff (hρ y hy) hy1 _).2 hmem

include H in
theorem card_CV_eq (X : Subgroup G) (hX : X ≤ L ⊔ QM L M) (hX2 : ∀ x ∈ X, x * x = 1)
    (hne : ¬ X ≤ QM L M) :
    Nat.card ↥(blockU L ⊓ Subgroup.centralizer (X : Set G)) = Nat.card (Fq n) := by
  obtain ⟨p, hp⟩ := H.exists_root_point X hX hX2
  obtain ⟨x, hxX, hxQ⟩ := IsConcreteLE.not_le_iff_exists.1 hne
  have hXM : X ≤ M := hX.trans (H.LQ_le)
  have hρ : ∀ y (hy : y ∈ X), H.rho ⟨y, hX hy⟩ ∈ rootGrp p := fun y hy => hp ⟨⟨y, hy⟩, rfl⟩
  have hx1 : H.rho ⟨x, hX hxX⟩ ≠ 1 := fun h => hxQ ((H.rho_eq_one_iff ⟨x, hX hxX⟩).1 h)
  rw [H.card_CV X hXM, ← card_submodule_line p]
  refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) fun w => ?_)
  constructor
  · intro h
    exact (H.fixed_iff (hρ x hxX) hx1 w).1 (h x hxX)
  · intro hw y hy
    by_cases hy1 : H.rho ⟨y, hX hy⟩ = 1
    · rw [H.actHom_eq_one_of_rho hy1]
      rfl
    · exact (H.fixed_iff (hρ y hy) hy1 w).2 hw

end MData

end CFSG.CGT.PushingUpLit.T2KR
