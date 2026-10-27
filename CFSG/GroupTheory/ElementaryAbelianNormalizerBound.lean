module

public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut

public section

namespace CFSG.GroupTheory

open Subgroup
open scoped IsMulCommutative

variable {G : Type*} [Group G]

private lemma card_mulAut_eq_card_GL {A : Subgroup G} [IsElementaryAbelian 2 A] {n : ℕ}
    (hA : Nat.card A = 2 ^ n) :
    Nat.card (MulAut ↥A) = Nat.card (GL (Fin n) (ZMod 2)) := by
  haveI : Finite ↥A :=
    Nat.finite_of_card_ne_zero (by rw [hA]; exact (pow_pos (by norm_num) n).ne')
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2)
    (W := ↥A) (fun a b => mul_comm' a b)
    (fun a => Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 A) a) (n := n) hA
  exact CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL (p := 2) e

private lemma card_GL_two_eq (n : ℕ) :
    Nat.card (GL (Fin n) (ZMod 2)) =
      2 ^ (n * (n - 1) / 2) * ∏ i : Fin n, (2 ^ (n - (i : ℕ)) - 1) := by
  rw [CFSG.SectionRank.Ccomm.card_GL_zmod (p := 2)]
  have hfac : ∀ i : Fin n, (2 : ℕ) ^ n - 2 ^ (i : ℕ) =
      2 ^ (i : ℕ) * (2 ^ (n - (i : ℕ)) - 1) := by
    intro i
    have hi : (i : ℕ) ≤ n := le_of_lt i.2
    rw [Nat.mul_sub_left_distrib, mul_one, pow_mul_pow_sub (2 : ℕ) hi]
  rw [Finset.prod_congr rfl (fun i _ => hfac i), Finset.prod_mul_distrib]
  congr 1
  calc ∏ i : Fin n, (2 : ℕ) ^ (i : ℕ)
      = 2 ^ (∑ i : Fin n, (i : ℕ)) := by
        simpa using (Finset.prod_pow_eq_pow_sum (Finset.univ : Finset (Fin n))
          (fun i => (i : ℕ)) 2)
    _ = 2 ^ (n * (n - 1) / 2) := by
        rw [Fin.sum_univ_eq_sum_range (fun i => i) n, Finset.sum_range_id]

private lemma card_le_two_pow_of_isPGroup_dvd_mul_odd {H : Type*} [Group H]
    {m O : ℕ} (h : IsPGroup 2 H) (hO : Odd O) (hdvd : Nat.card H ∣ 2 ^ m * O) :
    Nat.card H ≤ 2 ^ m := by
  have hNpos : 0 < 2 ^ m * O := by
    apply Nat.mul_pos (pow_pos (by norm_num) m)
    rcases hO with ⟨t, ht⟩
    omega
  haveI : Finite H := Nat.finite_of_card_ne_zero (Nat.pos_of_dvd_of_pos hdvd hNpos).ne'
  obtain ⟨t, ht⟩ := IsPGroup.iff_card.mp h
  rw [ht] at hdvd ⊢
  have hcop : Nat.Coprime (2 ^ t) O := (hO.coprime_two_right).symm.pow_left t
  have hdvd' : 2 ^ t ∣ 2 ^ m := hcop.dvd_of_dvd_mul_right hdvd
  have htle : t ≤ m := by
    have hle : 2 ^ t ≤ 2 ^ m := Nat.le_of_dvd (pow_pos (by norm_num) m) hdvd'
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
  exact Nat.pow_le_pow_right (by norm_num) htle

private noncomputable def conjHom {P A : Subgroup G}
    (hPN : P ≤ Subgroup.normalizer (A : Set G)) : ↥P →* MulAut ↥A :=
  A.normalizerMonoidHom.comp (Subgroup.inclusion hPN)

private lemma normalizerMonoidHom_apply_coe {H K : Subgroup G}
    (hK : K ≤ Subgroup.normalizer (H : Set G)) (x : ↥K) (y : ↥H) :
    ((H.normalizerMonoidHom (Subgroup.inclusion hK x)) y : G) =
      (x : G) * (y : G) * (x : G)⁻¹ := by
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  rfl

private lemma conjHom_apply_coe {P A : Subgroup G}
    (hPN : P ≤ Subgroup.normalizer (A : Set G)) (x : ↥P) (a : ↥A) :
    ((conjHom hPN x) a : G) = (x : G) * (a : G) * (x : G)⁻¹ := by
  rw [conjHom, MonoidHom.comp_apply, normalizerMonoidHom_apply_coe]

private lemma conjHom_ker {P A : Subgroup G}
    (hPN : P ≤ Subgroup.normalizer (A : Set G)) :
    (conjHom hPN).ker = (P ⊓ Subgroup.centralizer (A : Set G)).subgroupOf P := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · intro hx
    refine ⟨x.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have h := congrArg Subtype.val (DFunLike.congr_fun hx (⟨a, ha⟩ : ↥A))
    rw [conjHom_apply_coe, MulAut.one_apply] at h
    calc a * (x : G) = ((x : G) * a * (x : G)⁻¹) * (x : G) := by rw [h]
      _ = (x : G) * a := by group
  · rintro ⟨-, hx⟩
    apply MulEquiv.ext
    intro a
    apply Subtype.ext
    rw [conjHom_apply_coe, MulAut.one_apply]
    have hxinv : (x : G)⁻¹ ∈ Subgroup.centralizer (A : Set G) := Subgroup.inv_mem _ hx
    have h1 := Subgroup.mem_centralizer_iff.mp hxinv a a.2
    calc (x : G) * (a : G) * (x : G)⁻¹ = (x : G) * ((a : G) * (x : G)⁻¹) := by group
      _ = (x : G) * ((x : G)⁻¹ * (a : G)) := by rw [h1]
      _ = (a : G) := by group

private lemma card_ker_conjHom {P A : Subgroup G}
    (hPN : P ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card ↥(conjHom hPN).ker =
      Nat.card ↥(P ⊓ Subgroup.centralizer (A : Set G)) := by
  rw [conjHom_ker hPN]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv

theorem card_le_two_pow_mul_of_normalizes {A P : Subgroup G}
    [IsElementaryAbelian 2 A] {n : ℕ}
    (hA : Nat.card A = 2 ^ n) (hP : IsPGroup 2 P)
    (hPA : P ≤ normalizer (A : Set G)) :
    Nat.card P ≤ 2 ^ (n * (n - 1) / 2) * Nat.card ↥(P ⊓ centralizer (A : Set G)) := by
  classical
  let φ : ↥P →* MulAut ↥A := conjHom hPA
  have hφker : Nat.card ↥φ.ker = Nat.card ↥(P ⊓ centralizer (A : Set G)) :=
    card_ker_conjHom hPA
  have hodd : Odd (∏ i : Fin n, (2 ^ (n - (i : ℕ)) - 1)) := by
    refine Finset.prod_induction (fun i : Fin n => 2 ^ (n - (i : ℕ)) - 1) (Odd ·)
      (fun a b ha hb => ha.mul hb) odd_one ?_
    intro i _
    have hi : 0 < n - (i : ℕ) := by
      have := i.2
      omega
    have h1 : 1 ≤ 2 ^ (n - (i : ℕ)) := Nat.one_le_pow _ _ (by norm_num)
    have he : Even (2 ^ (n - (i : ℕ))) :=
      even_iff_two_dvd.mpr (dvd_pow_self 2 hi.ne')
    exact Nat.Even.sub_odd h1 he odd_one
  have hφrange : Nat.card ↥φ.range ≤ 2 ^ (n * (n - 1) / 2) := by
    have hp2 : IsPGroup 2 ↥φ.range :=
      hP.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
    have hdvd : Nat.card ↥φ.range ∣ Nat.card (GL (Fin n) (ZMod 2)) := by
      have h1 : Nat.card ↥φ.range ∣ Nat.card (MulAut ↥A) :=
        Subgroup.card_subgroup_dvd_card φ.range
      rwa [card_mulAut_eq_card_GL hA] at h1
    rw [card_GL_two_eq n] at hdvd
    exact card_le_two_pow_of_isPGroup_dvd_mul_odd hp2 hodd hdvd
  calc Nat.card P = Nat.card ↥φ.ker * Nat.card ↥φ.range :=
        (Subgroup.card_ker_mul_card_range φ).symm
    _ = Nat.card ↥(P ⊓ centralizer (A : Set G)) * Nat.card ↥φ.range := by rw [hφker]
    _ ≤ Nat.card ↥(P ⊓ centralizer (A : Set G)) * 2 ^ (n * (n - 1) / 2) :=
        Nat.mul_le_mul_left _ hφrange
    _ = 2 ^ (n * (n - 1) / 2) * Nat.card ↥(P ⊓ centralizer (A : Set G)) :=
        Nat.mul_comm _ _

private noncomputable def psi {A : Subgroup G} [IsElementaryAbelian 2 A] {u : G}
    (huA : ∀ a ∈ A, u * a * u⁻¹ ∈ A) : ↥A →* ↥A where
  toFun a := ⟨(a : G)⁻¹ * (u * (a : G) * u⁻¹), mul_mem (inv_mem a.2) (huA a a.2)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := by
    have ha : u * (a : G) * u⁻¹ ∈ A := huA a a.2
    have hb : u * (b : G) * u⁻¹ ∈ A := huA b b.2
    have hba : (b : G)⁻¹ * (a : G)⁻¹ = (a : G)⁻¹ * (b : G)⁻¹ :=
      congrArg Subtype.val (mul_comm' (⟨(b : G)⁻¹, inv_mem b.2⟩ : ↥A)
        (⟨(a : G)⁻¹, inv_mem a.2⟩ : ↥A))
    have hbxa : (b : G)⁻¹ * (u * (a : G) * u⁻¹) =
        (u * (a : G) * u⁻¹) * (b : G)⁻¹ :=
      congrArg Subtype.val (mul_comm' (⟨(b : G)⁻¹, inv_mem b.2⟩ : ↥A)
        (⟨u * (a : G) * u⁻¹, ha⟩ : ↥A))
    refine Subtype.ext ?_
    show ((a : G) * (b : G))⁻¹ * (u * ((a : G) * (b : G)) * u⁻¹) =
      ((a : G)⁻¹ * (u * (a : G) * u⁻¹)) * ((b : G)⁻¹ * (u * (b : G) * u⁻¹))
    rw [show ((a : G) * (b : G))⁻¹ = (b : G)⁻¹ * (a : G)⁻¹ from by group]
    rw [show u * ((a : G) * (b : G)) * u⁻¹ =
      (u * (a : G) * u⁻¹) * (u * (b : G) * u⁻¹) from by group]
    calc (b : G)⁻¹ * (a : G)⁻¹ * ((u * (a : G) * u⁻¹) * (u * (b : G) * u⁻¹))
        = (a : G)⁻¹ * (b : G)⁻¹ * ((u * (a : G) * u⁻¹) * (u * (b : G) * u⁻¹)) := by
          rw [hba]
      _ = (a : G)⁻¹ * ((b : G)⁻¹ * (u * (a : G) * u⁻¹)) * (u * (b : G) * u⁻¹) := by group
      _ = (a : G)⁻¹ * ((u * (a : G) * u⁻¹) * (b : G)⁻¹) * (u * (b : G) * u⁻¹) := by
          rw [hbxa]
      _ = (a : G)⁻¹ * (u * (a : G) * u⁻¹) * ((b : G)⁻¹ * (u * (b : G) * u⁻¹)) := by group

private lemma psi_fixed {A : Subgroup G} [IsElementaryAbelian 2 A] {u : G}
    (huA : ∀ a ∈ A, u * a * u⁻¹ ∈ A)
    (hu2 : ∀ a ∈ A, u ^ 2 * a * (u ^ 2)⁻¹ = a) (a : ↥A) :
    u * (psi huA a : G) * u⁻¹ = psi huA a := by
  have ha : (a : G) ∈ A := a.2
  have hb : u * (a : G) * u⁻¹ ∈ A := huA a a.2
  have hainv : (a : G)⁻¹ = (a : G) := by
    have h2 : (a : G) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (a : G) a.2
    exact inv_eq_of_mul_eq_one_right (by simpa [pow_two] using h2)
  have h2 : u * (u * (a : G) * u⁻¹) * u⁻¹ = (a : G) := by
    calc u * (u * (a : G) * u⁻¹) * u⁻¹ = (u * u) * (a : G) * (u * u)⁻¹ := by group
      _ = u ^ 2 * (a : G) * (u ^ 2)⁻¹ := by rw [pow_two]
      _ = (a : G) := hu2 a a.2
  show u * ((a : G)⁻¹ * (u * (a : G) * u⁻¹)) * u⁻¹ =
    (a : G)⁻¹ * (u * (a : G) * u⁻¹)
  calc u * ((a : G)⁻¹ * (u * (a : G) * u⁻¹)) * u⁻¹
      = (u * (a : G)⁻¹ * u⁻¹) * (u * (u * (a : G) * u⁻¹) * u⁻¹) := by group
    _ = (u * (a : G) * u⁻¹) * (a : G) := by rw [h2, hainv]
    _ = (a : G) * (u * (a : G) * u⁻¹) :=
        (congrArg Subtype.val (mul_comm' (⟨(a : G), ha⟩ : ↥A)
          (⟨u * (a : G) * u⁻¹, hb⟩ : ↥A))).symm
    _ = (a : G)⁻¹ * (u * (a : G) * u⁻¹) := by rw [hainv]

private lemma psi_conj {A P : Subgroup G} [IsElementaryAbelian 2 A] {u : G}
    (huA : ∀ a ∈ A, u * a * u⁻¹ ∈ A)
    (hPA : ∀ x ∈ P, ∀ a ∈ A, x * a * x⁻¹ ∈ A)
    (hPu : ∀ x ∈ P, ∀ a ∈ A,
      (x * u * x⁻¹ * u⁻¹) * a * (x * u * x⁻¹ * u⁻¹)⁻¹ = a)
    {x : G} (hx : x ∈ P) (a : ↥A) :
    psi huA ⟨x * (a : G) * x⁻¹, hPA x hx a a.2⟩ =
      ⟨x * (psi huA a : G) * x⁻¹, hPA x hx _ (psi huA a).2⟩ := by
  have hb : x * (a : G) * x⁻¹ ∈ A := hPA x hx a a.2
  have hkey : u * (x * (a : G) * x⁻¹) * u⁻¹ = x * (u * (a : G) * u⁻¹) * x⁻¹ := by
    have hu1 : x * u * x⁻¹ = (x * u * x⁻¹ * u⁻¹) * u := by group
    have hmid : (x * u * x⁻¹) * (x * (a : G) * x⁻¹) * (x * u * x⁻¹)⁻¹ =
        u * (x * (a : G) * x⁻¹) * u⁻¹ := by
      rw [hu1]
      have hb2 : u * (x * (a : G) * x⁻¹) * u⁻¹ ∈ A := huA _ hb
      calc (x * u * x⁻¹ * u⁻¹ * u) * (x * (a : G) * x⁻¹) * (x * u * x⁻¹ * u⁻¹ * u)⁻¹
          = (x * u * x⁻¹ * u⁻¹) * (u * (x * (a : G) * x⁻¹) * u⁻¹) *
              (x * u * x⁻¹ * u⁻¹)⁻¹ := by group
        _ = u * (x * (a : G) * x⁻¹) * u⁻¹ := hPu x hx _ hb2
    calc u * (x * (a : G) * x⁻¹) * u⁻¹
        = (x * u * x⁻¹) * (x * (a : G) * x⁻¹) * (x * u * x⁻¹)⁻¹ := hmid.symm
      _ = x * (u * (a : G) * u⁻¹) * x⁻¹ := by group
  refine Subtype.ext ?_
  show (x * (a : G) * x⁻¹)⁻¹ * (u * (x * (a : G) * x⁻¹) * u⁻¹) =
    x * ((a : G)⁻¹ * (u * (a : G) * u⁻¹)) * x⁻¹
  rw [hkey]
  group

private lemma psi_ker {A : Subgroup G} [IsElementaryAbelian 2 A] {u : G}
    (huA : ∀ a ∈ A, u * a * u⁻¹ ∈ A) :
    (psi huA).ker = (A ⊓ Subgroup.centralizer ({u} : Set G)).subgroupOf A := by
  ext a
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    refine ⟨a.2, ?_⟩
    have h' : (a : G)⁻¹ * (u * (a : G) * u⁻¹) = 1 := congrArg Subtype.val h
    have h'' : (a : G) = u * (a : G) * u⁻¹ := inv_mul_eq_one.mp h'
    calc (a : G) * u = (u * (a : G) * u⁻¹) * u := by rw [← h'']
      _ = u * (a : G) := by group
  · rintro ⟨-, ha⟩
    refine Subtype.ext ?_
    show (a : G)⁻¹ * (u * (a : G) * u⁻¹) = 1
    have h2 : u * (a : G) * u⁻¹ = (a : G) := by
      rw [← ha]
      group
    rw [h2, inv_mul_cancel]

private lemma psi_range {A : Subgroup G} [IsElementaryAbelian 2 A] {u : G}
    (huA : ∀ a ∈ A, u * a * u⁻¹ ∈ A)
    (hu2 : ∀ a ∈ A, u ^ 2 * a * (u ^ 2)⁻¹ = a) {k : ℕ}
    (hA : Nat.card A = 2 ^ (2 * k))
    (hY : Nat.card ↥(A ⊓ Subgroup.centralizer ({u} : Set G)) = 2 ^ k) :
    (psi huA).range = (A ⊓ Subgroup.centralizer ({u} : Set G)).subgroupOf A := by
  haveI : Finite ↥A :=
    Nat.finite_of_card_ne_zero (by rw [hA]; exact (pow_pos (by norm_num) _).ne')
  haveI : Finite ↥((A ⊓ Subgroup.centralizer ({u} : Set G)).subgroupOf A) := Subtype.finite
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨a, rfl⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    refine ⟨(psi huA a).2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (psi huA a) * u = (u * (psi huA a) * u⁻¹) * u := by
          rw [psi_fixed huA hu2 a]
      _ = u * (psi huA a) := by group
  · have h1 := Subgroup.card_ker_mul_card_range (psi huA)
    rw [psi_ker huA] at h1
    have hYc : Nat.card ↥((A ⊓ Subgroup.centralizer ({u} : Set G)).subgroupOf A) = 2 ^ k := by
      rw [← hY]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    rw [hYc, hA] at h1
    have h2 : Nat.card ↥(psi huA).range = 2 ^ k := by
      have hpos : 0 < 2 ^ k := pow_pos (by norm_num) k
      have h1' : 2 ^ k * Nat.card ↥(psi huA).range = 2 ^ k * 2 ^ k := by
        rw [h1, show 2 * k = k + k by ring, pow_add]
      exact Nat.mul_left_cancel hpos h1'
    rw [hYc, h2]

theorem card_le_card_inf_centralizer_sq {Y : Subgroup G} [IsElementaryAbelian 2 Y] {x : G}
    (hxY : x ∈ normalizer (Y : Set G)) (hx2 : x ^ 2 ∈ centralizer (Y : Set G)) :
    Nat.card Y ≤ Nat.card ↥(Y ⊓ centralizer ({x} : Set G)) ^ 2 := by
  classical
  by_cases hfin : Finite ↥Y
  · haveI := hfin
    letI : CommGroup ↥Y :=
      { (inferInstance : Group ↥Y) with mul_comm := fun a b => mul_comm' a b }
    have hxY' : ∀ a ∈ Y, x * a * x⁻¹ ∈ Y :=
      fun a ha => (Subgroup.mem_normalizer_iff.mp hxY a).1 ha
    have hx2' : ∀ a ∈ Y, x ^ 2 * a * (x ^ 2)⁻¹ = a := by
      intro a ha
      have h := Subgroup.mem_centralizer_iff.mp hx2 a ha
      calc x ^ 2 * a * (x ^ 2)⁻¹ = (a * x ^ 2) * (x ^ 2)⁻¹ := by rw [h]
        _ = a := by group
    let α : ↥Y →* ↥Y :=
      { toFun := fun a => ⟨x * a * x⁻¹, hxY' a a.2⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
    let μ : ↥Y →* ↥Y :=
      { toFun := fun a => a * α a
        map_one' := by simp
        map_mul' := fun a b => by
          show (a * b) * α (a * b) = (a * α a) * (b * α b)
          rw [map_mul]
          ac_rfl }
    have hker : μ.ker = (Y ⊓ centralizer ({x} : Set G)).subgroupOf Y := by
      ext a
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
        Subgroup.mem_centralizer_singleton_iff]
      constructor
      · intro h
        have h' : (a : G) * (x * (a : G) * x⁻¹) = 1 := congrArg Subtype.val h
        have hα : x * (a : G) * x⁻¹ = (a : G) := by
          have hαinv : x * (a : G) * x⁻¹ = (a : G)⁻¹ := eq_inv_of_mul_eq_one_right h'
          have ha : (a : G)⁻¹ = (a : G) := by
            have h2 : (a : G) ^ 2 = 1 :=
              elemPow_eq_one_of_isElementaryAbelian (a : G) a.2
            exact inv_eq_of_mul_eq_one_right (by simpa [pow_two] using h2)
          rw [hαinv, ha]
        exact ⟨a.2, (mul_inv_eq_iff_eq_mul.mp hα).symm⟩
      · rintro ⟨-, hcent⟩
        have hα : x * (a : G) * x⁻¹ = (a : G) := by
          calc x * (a : G) * x⁻¹ = ((a : G) * x) * x⁻¹ := by rw [← hcent]
            _ = (a : G) := by group
        apply Subtype.ext
        show (a : G) * (x * (a : G) * x⁻¹) = 1
        rw [hα]
        have h2 : (a : G) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (a : G) a.2
        simpa [pow_two] using h2
    have hrange : μ.range ≤ (Y ⊓ centralizer ({x} : Set G)).subgroupOf Y := by
      rintro _ ⟨a, rfl⟩
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      refine ⟨(μ a).2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hfix : x * (μ a : G) * x⁻¹ = (μ a : G) := by
        show x * ((a : G) * (x * (a : G) * x⁻¹)) * x⁻¹ =
          (a : G) * (x * (a : G) * x⁻¹)
        have hxx : x * (x * (a : G) * x⁻¹) * x⁻¹ = (a : G) := by
          calc x * (x * (a : G) * x⁻¹) * x⁻¹
              = (x * x) * (a : G) * ((x * x)⁻¹) := by group
            _ = x ^ 2 * (a : G) * (x ^ 2)⁻¹ := by rw [pow_two]
            _ = (a : G) := hx2' a a.2
        calc x * ((a : G) * (x * (a : G) * x⁻¹)) * x⁻¹
            = (x * (a : G) * x⁻¹) * (x * (x * (a : G) * x⁻¹) * x⁻¹) := by group
          _ = (x * (a : G) * x⁻¹) * (a : G) := by rw [hxx]
          _ = (a : G) * (x * (a : G) * x⁻¹) :=
              congrArg Subtype.val (mul_comm' (⟨x * (a : G) * x⁻¹, hxY' a a.2⟩ : ↥Y)
                (⟨(a : G), a.2⟩ : ↥Y))
      exact (mul_inv_eq_iff_eq_mul.mp hfix).symm
    have hkercard : Nat.card ↥μ.ker = Nat.card ↥(Y ⊓ centralizer ({x} : Set G)) := by
      rw [hker]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    have hrangcard : Nat.card ↥μ.range ≤ Nat.card ↥(Y ⊓ centralizer ({x} : Set G)) := by
      have h := Subgroup.card_le_of_le hrange
      have hEq : Nat.card ↥((Y ⊓ centralizer ({x} : Set G)).subgroupOf Y) =
          Nat.card ↥(Y ⊓ centralizer ({x} : Set G)) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
      rwa [hEq] at h
    calc Nat.card Y = Nat.card ↥μ.ker * Nat.card ↥μ.range :=
          (Subgroup.card_ker_mul_card_range μ).symm
      _ = Nat.card ↥(Y ⊓ centralizer ({x} : Set G)) * Nat.card ↥μ.range := by rw [hkercard]
      _ ≤ Nat.card ↥(Y ⊓ centralizer ({x} : Set G)) ^ 2 := by
          rw [pow_two]
          exact Nat.mul_le_mul_left _ hrangcard
  · haveI : Infinite ↥Y := not_finite_iff_infinite.mp hfin
    rw [Nat.card_eq_zero_of_infinite]
    exact Nat.zero_le _

theorem card_le_two_pow_mul_of_centralizes_involution_mod {A P : Subgroup G}
    [IsElementaryAbelian 2 A] {k : ℕ}
    (hA : Nat.card A = 2 ^ (2 * k)) (hP : IsPGroup 2 P)
    (hPA : P ≤ normalizer (A : Set G))
    {u : G} (huA : u ∈ normalizer (A : Set G)) (hu2 : u ^ 2 ∈ centralizer (A : Set G))
    (hfix : Nat.card ↥(A ⊓ centralizer ({u} : Set G)) = 2 ^ k)
    (hPu : ∀ x ∈ P, x * u * x⁻¹ * u⁻¹ ∈ centralizer (A : Set G)) :
    Nat.card P ≤ 2 ^ (k * (k - 1) / 2 + k * k) *
      Nat.card ↥(P ⊓ centralizer (A : Set G)) := by
  classical
  haveI : Finite ↥A :=
    Nat.finite_of_card_ne_zero (by rw [hA]; exact (pow_pos (by norm_num) _).ne')
  have hPA' : ∀ x ∈ P, ∀ a ∈ A, x * a * x⁻¹ ∈ A :=
    fun x hx a ha => (Subgroup.mem_normalizer_iff.mp (hPA hx) a).1 ha
  have huA' : ∀ a ∈ A, u * a * u⁻¹ ∈ A :=
    fun a ha => (Subgroup.mem_normalizer_iff.mp huA a).1 ha
  have hu2' : ∀ a ∈ A, u ^ 2 * a * (u ^ 2)⁻¹ = a := by
    intro a ha
    have h := Subgroup.mem_centralizer_iff.mp hu2 a ha
    calc u ^ 2 * a * (u ^ 2)⁻¹ = (a * u ^ 2) * (u ^ 2)⁻¹ := by rw [h]
      _ = a := by group
  have hPu' : ∀ x ∈ P, ∀ a ∈ A,
      (x * u * x⁻¹ * u⁻¹) * a * (x * u * x⁻¹ * u⁻¹)⁻¹ = a := by
    intro x hx a ha
    have h := Subgroup.mem_centralizer_iff.mp (hPu x hx) a ha
    calc (x * u * x⁻¹ * u⁻¹) * a * (x * u * x⁻¹ * u⁻¹)⁻¹
        = (a * (x * u * x⁻¹ * u⁻¹)) * (x * u * x⁻¹ * u⁻¹)⁻¹ := by rw [h]
      _ = a := by group
  set Y : Subgroup G := A ⊓ centralizer ({u} : Set G) with hYdef
  have hYle : Y ≤ A := inf_le_left
  have hY : Nat.card Y = 2 ^ k := hfix
  haveI : IsElementaryAbelian 2 Y := IsElementaryAbelian.of_le inferInstance hYle
  haveI : Finite ↥Y :=
    Nat.finite_of_card_ne_zero (by rw [hY]; exact (pow_pos (by norm_num) _).ne')
  set Ysub : Subgroup ↥A := Y.subgroupOf A with hYsubdef
  have hYsub : Nat.card ↥Ysub = 2 ^ k := by
    rw [← hY]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYle).toEquiv
  haveI : IsElementaryAbelian 2 Ysub := IsElementaryAbelian.subgroupOf hYle
  let ψ : ↥A →* ↥A := psi huA'
  have hψker : ψ.ker = Ysub := by
    rw [hYsubdef, hYdef]
    exact psi_ker huA'
  have hψrange : ψ.range = Ysub := by
    rw [hYsubdef, hYdef]
    exact psi_range huA' hu2' hA hfix
  have hPNY : P ≤ Subgroup.normalizer (Y : Set G) := by
    have hfwd : ∀ x ∈ P, ∀ y ∈ Y, x * y * x⁻¹ ∈ Y := by
      intro x hx y hy
      have hyA : y ∈ A := hYle hy
      have hyrange : (⟨y, hyA⟩ : ↥A) ∈ ψ.range := by
        rw [hψrange]
        exact hy
      obtain ⟨a, ha⟩ := hyrange
      have hya : (ψ a : G) = y := congrArg Subtype.val ha
      have hmemψ : (ψ ⟨x * (a : G) * x⁻¹, hPA' x hx a a.2⟩ : ↥A) ∈ ψ.range := ⟨_, rfl⟩
      have hmemY : (ψ ⟨x * (a : G) * x⁻¹, hPA' x hx a a.2⟩ : G) ∈ Y := by
        rw [hψrange] at hmemψ
        exact hmemψ
      have hconj : x * (ψ a : G) * x⁻¹ ∈ Y := by
        have h2 := hmemY
        rw [psi_conj huA' hPA' hPu' hx a] at h2
        exact h2
      rwa [hya] at hconj
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    exact ⟨fun hy => hfwd x hx y hy, fun hy => by
      have h := hfwd x⁻¹ (Subgroup.inv_mem P hx) (x * y * x⁻¹) hy
      rwa [show x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y from by group] at h⟩
  have hPbound : Nat.card P ≤ 2 ^ (k * (k - 1) / 2) *
      Nat.card ↥(P ⊓ centralizer (Y : Set G)) :=
    card_le_two_pow_mul_of_normalizes (A := Y) (P := P) hY hP hPNY
  set P₁ : Subgroup G := P ⊓ centralizer (Y : Set G) with hP₁def
  have hP₁le : P₁ ≤ P := inf_le_left
  have hP₁Y : ∀ x ∈ P₁, ∀ y ∈ Y, (x : G) * y * (x : G)⁻¹ = y := by
    intro x hx y hy
    have h := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2 y hy
    calc (x : G) * y * (x : G)⁻¹ = (y * (x : G)) * (x : G)⁻¹ := by rw [← h]
      _ = y := by group
  have hFY : ∀ x ∈ P₁, ∀ a : ↥A, (a : G)⁻¹ * ((x : G) * a * (x : G)⁻¹) ∈ Y := by
    intro x hx a
    have hxP : (x : G) ∈ P := hP₁le hx
    have hmem : (a : G)⁻¹ * ((x : G) * (a : G) * (x : G)⁻¹) ∈ A :=
      mul_mem (inv_mem a.2) (hPA' x hxP a a.2)
    have h1 : ψ ⟨(a : G)⁻¹ * ((x : G) * (a : G) * (x : G)⁻¹), hmem⟩ = 1 := by
      have hmul := map_mul ψ (⟨(a : G)⁻¹, inv_mem a.2⟩ : ↥A)
        (⟨(x : G) * (a : G) * (x : G)⁻¹, hPA' x hxP a a.2⟩ : ↥A)
      rw [show ((⟨(a : G)⁻¹, inv_mem a.2⟩ : ↥A) *
          ⟨(x : G) * (a : G) * (x : G)⁻¹, hPA' x hxP a a.2⟩ : ↥A) =
          ⟨(a : G)⁻¹ * ((x : G) * (a : G) * (x : G)⁻¹), hmem⟩ from Subtype.ext rfl] at hmul
      have hainv : ψ ⟨(a : G)⁻¹, inv_mem a.2⟩ = (ψ a)⁻¹ := by
        have h := map_inv ψ a
        rwa [show (a : ↥A)⁻¹ = ⟨(a : G)⁻¹, inv_mem a.2⟩ from rfl] at h
      have hpsiY : (ψ a : G) ∈ Y := by
        have h : ψ a ∈ ψ.range := ⟨a, rfl⟩
        rw [hψrange] at h
        exact h
      have hconj : ψ ⟨x * (a : G) * x⁻¹, hPA' x hxP a a.2⟩ = ψ a := by
        rw [psi_conj huA' hPA' hPu' hxP a]
        apply Subtype.ext
        show (x : G) * (ψ a : G) * (x : G)⁻¹ = (ψ a : G)
        exact hP₁Y x hx _ hpsiY
      rw [hmul, hainv, hconj, inv_mul_cancel]
    have h1' : (⟨(a : G)⁻¹ * ((x : G) * (a : G) * (x : G)⁻¹), hmem⟩ : ↥A) ∈ ψ.ker := h1
    rw [hψker, Subgroup.mem_subgroupOf] at h1'
    exact h1'
  let fx : ↥P₁ → (↥A →* ↥Y) := fun x =>
    { toFun := fun a => ⟨(a : G)⁻¹ * ((x : G) * a * (x : G)⁻¹), hFY x x.2 a⟩
      map_one' := Subtype.ext (by
        show ((1 : ↥A) : G)⁻¹ * ((x : G) * ((1 : ↥A) : G) * (x : G)⁻¹) = 1
        simp)
      map_mul' := fun a b => Subtype.ext (by
        have ha : (a : G) ∈ A := a.2
        have hb : (b : G) ∈ A := b.2
        have ha' : (x : G) * (a : G) * (x : G)⁻¹ ∈ A := hPA' x (hP₁le x.2) a a.2
        have hb' : (x : G) * (b : G) * (x : G)⁻¹ ∈ A := hPA' x (hP₁le x.2) b b.2
        have hba : (b : G)⁻¹ * (a : G)⁻¹ = (a : G)⁻¹ * (b : G)⁻¹ :=
          congrArg Subtype.val (mul_comm' (⟨(b : G)⁻¹, inv_mem b.2⟩ : ↥A)
            (⟨(a : G)⁻¹, inv_mem a.2⟩ : ↥A))
        have hbxa : (b : G)⁻¹ * ((x : G) * (a : G) * (x : G)⁻¹) =
            ((x : G) * (a : G) * (x : G)⁻¹) * (b : G)⁻¹ :=
          congrArg Subtype.val (mul_comm' (⟨(b : G)⁻¹, inv_mem b.2⟩ : ↥A)
            (⟨(x : G) * (a : G) * (x : G)⁻¹, ha'⟩ : ↥A))
        show ((a : G) * (b : G))⁻¹ * ((x : G) * ((a : G) * (b : G)) * (x : G)⁻¹) =
          ((a : G)⁻¹ * ((x : G) * (a : G) * (x : G)⁻¹)) *
            ((b : G)⁻¹ * ((x : G) * (b : G) * (x : G)⁻¹))
        rw [show ((a : G) * (b : G))⁻¹ = (b : G)⁻¹ * (a : G)⁻¹ from by group]
        rw [show (x : G) * ((a : G) * (b : G)) * (x : G)⁻¹ =
          ((x : G) * (a : G) * (x : G)⁻¹) * ((x : G) * (b : G) * (x : G)⁻¹) from by group]
        calc (b : G)⁻¹ * (a : G)⁻¹ *
              (((x : G) * (a : G) * (x : G)⁻¹) * ((x : G) * (b : G) * (x : G)⁻¹))
            = (a : G)⁻¹ * (b : G)⁻¹ *
              (((x : G) * (a : G) * (x : G)⁻¹) * ((x : G) * (b : G) * (x : G)⁻¹)) := by
              rw [hba]
          _ = (a : G)⁻¹ * ((b : G)⁻¹ * ((x : G) * (a : G) * (x : G)⁻¹)) *
              ((x : G) * (b : G) * (x : G)⁻¹) := by group
          _ = (a : G)⁻¹ * (((x : G) * (a : G) * (x : G)⁻¹) * (b : G)⁻¹) *
              ((x : G) * (b : G) * (x : G)⁻¹) := by rw [hbxa]
          _ = (a : G)⁻¹ * ((x : G) * (a : G) * (x : G)⁻¹) *
              ((b : G)⁻¹ * ((x : G) * (b : G) * (x : G)⁻¹)) := by group) }
  let F : ↥P₁ →* (↥A →* ↥Y) :=
    { toFun := fx
      map_one' := MonoidHom.ext (fun a => Subtype.ext (by
        show ((a : G)⁻¹ * ((1 : G) * (a : G) * (1 : G)⁻¹)) = 1
        simp))
      map_mul' := fun x y => MonoidHom.ext (fun a => Subtype.ext (by
        show ((a : G)⁻¹ * (((x : G) * (y : G)) * (a : G) * ((x : G) * (y : G))⁻¹)) =
          ((a : G)⁻¹ * ((x : G) * (a : G) * (x : G)⁻¹)) *
            ((a : G)⁻¹ * ((y : G) * (a : G) * (y : G)⁻¹))
        have hxg : (x : G) * ((a : G)⁻¹ * ((y : G) * (a : G) * (y : G)⁻¹)) * (x : G)⁻¹ =
            (a : G)⁻¹ * ((y : G) * (a : G) * (y : G)⁻¹) := hP₁Y x x.2 _ (hFY y y.2 a)
        calc (a : G)⁻¹ * (((x : G) * (y : G)) * (a : G) * ((x : G) * (y : G))⁻¹)
            = (a : G)⁻¹ * ((x : G) * ((y : G) * (a : G) * (y : G)⁻¹) * (x : G)⁻¹) := by group
          _ = (a : G)⁻¹ * ((x : G) *
                ((a : G) * ((a : G)⁻¹ * ((y : G) * (a : G) * (y : G)⁻¹))) * (x : G)⁻¹) := by
              group
          _ = ((a : G)⁻¹ * ((x : G) * (a : G) * (x : G)⁻¹)) *
                ((x : G) * ((a : G)⁻¹ * ((y : G) * (a : G) * (y : G)⁻¹)) * (x : G)⁻¹) := by
              group
          _ = ((a : G)⁻¹ * ((x : G) * (a : G) * (x : G)⁻¹)) *
                ((a : G)⁻¹ * ((y : G) * (a : G) * (y : G)⁻¹)) := by rw [hxg])) }
  have hFker : Nat.card ↥F.ker = Nat.card ↥(P ⊓ centralizer (A : Set G)) := by
    have heq : F.ker = (P ⊓ centralizer (A : Set G)).subgroupOf P₁ := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      constructor
      · intro hx
        refine ⟨(Subgroup.mem_inf.mp x.2).1, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        have h := congrArg (fun f : ↥A →* ↥Y => ((f ⟨a, ha⟩ : ↥Y) : G)) hx
        simp only [MonoidHom.one_apply, Subtype.coe_mk] at h
        have h' : (a : G)⁻¹ * ((x : G) * (a : G) * (x : G)⁻¹) = 1 := h
        have h'' : (x : G) * (a : G) * (x : G)⁻¹ = (a : G) := (inv_mul_eq_one.mp h').symm
        calc (a : G) * (x : G) = ((x : G) * (a : G) * (x : G)⁻¹) * (x : G) := by rw [h'']
          _ = (x : G) * (a : G) := by group
      · rintro ⟨-, hx⟩
        apply MonoidHom.ext
        intro a
        apply Subtype.ext
        show (a : G)⁻¹ * ((x : G) * (a : G) * (x : G)⁻¹) = 1
        have h := Subgroup.mem_centralizer_iff.mp hx a a.2
        have h2 : (x : G) * (a : G) * (x : G)⁻¹ = (a : G) := by
          rw [show (x : G) * (a : G) = (a : G) * (x : G) from h.symm]
          group
        rw [h2, inv_mul_cancel]
    rw [heq]
    have hKle : P ⊓ centralizer (A : Set G) ≤ P₁ := by
      refine inf_le_inf_left _ ?_
      intro x hx
      exact Subgroup.mem_centralizer_iff.mpr
        (fun y hy => Subgroup.mem_centralizer_iff.mp hx y (hYle hy))
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKle).toEquiv
  have hkill : ∀ (z : ↥P₁) (b : ↥A), b ∈ Ysub → fx z b = 1 := by
    intro z b hb
    have hbY : (b : G) ∈ Y := hb
    apply Subtype.ext
    show (b : G)⁻¹ * ((z : G) * (b : G) * (z : G)⁻¹) = 1
    rw [hP₁Y z z.2 (b : G) hbY, inv_mul_cancel]
  let inc : ↥Ysub →* ↥A := Ysub.subtype
  let Linc : Additive ↥Ysub →ₗ[ZMod 2] Additive ↥A :=
    (MonoidHom.toAdditive inc).toZModLinearMap 2
  let W : Submodule (ZMod 2) (Additive ↥A) := Linc.range
  have hLinc_apply (y : Additive ↥Ysub) :
      Linc y = Additive.ofMul ((y.toMul : ↥Ysub) : ↥A) := by
    change (MonoidHom.toAdditive inc).toZModLinearMap 2 y = _
    rw [AddMonoidHom.coe_toZModLinearMap, MonoidHom.coe_toAdditive]
    rfl
  have hLinc_inj : Function.Injective Linc := by
    intro x y h
    change Additive.ofMul ((x.toMul : ↥Ysub) : ↥A) =
      Additive.ofMul ((y.toMul : ↥Ysub) : ↥A) at h
    have h2 : ((x.toMul : ↥Ysub) : ↥A) = ((y.toMul : ↥Ysub) : ↥A) :=
      Additive.ofMul.injective h
    have h3 : x.toMul = y.toMul := Subtype.val_injective h2
    exact Additive.toMul.injective h3
  have hcardW : Nat.card W = 2 ^ k := by
    have h := (LinearEquiv.ofInjective Linc hLinc_inj).toEquiv
    calc Nat.card W = Nat.card (Additive ↥Ysub) := (Nat.card_congr h).symm
      _ = Nat.card ↥Ysub := Nat.card_congr Additive.toMul
      _ = 2 ^ k := hYsub
  have hfinA : Module.finrank (ZMod 2) (Additive ↥A) = 2 * k := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive ↥A)
    rw [Nat.card_zmod] at h
    have hc : Nat.card (Additive ↥A) = 2 ^ (2 * k) := by
      rw [Nat.card_congr Additive.toMul, hA]
    rw [hc] at h
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 2) h).symm
  have hfinY : Module.finrank (ZMod 2) (Additive ↥Y) = k := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive ↥Y)
    rw [Nat.card_zmod] at h
    have hc : Nat.card (Additive ↥Y) = 2 ^ k := by
      rw [Nat.card_congr Additive.toMul, hY]
    rw [hc] at h
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 2) h).symm
  have hfinW : Module.finrank (ZMod 2) W = k := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)
    rw [Nat.card_zmod] at h
    rw [hcardW] at h
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 2) h).symm
  have hfinQuot : Module.finrank (ZMod 2) ((Additive ↥A) ⧸ W) = k := by
    have h := Submodule.finrank_quotient_add_finrank (R := ZMod 2) (M := Additive ↥A) W
    rw [hfinA, hfinW] at h
    omega
  have hcardLM : Nat.card ((Additive ↥A) ⧸ W →ₗ[ZMod 2] Additive ↥Y) = 2 ^ (k * k) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2)
        (V := (Additive ↥A) ⧸ W →ₗ[ZMod 2] Additive ↥Y),
      Nat.card_zmod, Module.finrank_linearMap, hfinQuot, hfinY]
  let Φ : ↥F.range → ((Additive ↥A) ⧸ W →ₗ[ZMod 2] Additive ↥Y) := fun f =>
    W.liftQ ((f : ↥A →* ↥Y).toAdditive.toZModLinearMap 2) (by
      rintro w ⟨y, rfl⟩
      have hf1 : (f : ↥A →* ↥Y) ((y.toMul : ↥Ysub) : ↥A) = 1 := by
        obtain ⟨z, hz⟩ := f.2
        rw [← hz]
        exact hkill z (y.toMul : ↥A) y.2
      rw [LinearMap.mem_ker, hLinc_apply, AddMonoidHom.coe_toZModLinearMap]
      change Additive.ofMul ((f : ↥A →* ↥Y) ((y.toMul : ↥Ysub) : ↥A)) = 0
      rw [hf1]
      rfl)
  have hΦinj : Function.Injective Φ := by
    intro f g hfg
    have hL : ((f : ↥A →* ↥Y).toAdditive.toZModLinearMap 2) =
        ((g : ↥A →* ↥Y).toAdditive.toZModLinearMap 2) := by
      have h := congrArg (fun L => L.comp W.mkQ) hfg
      simpa [Φ, Submodule.liftQ_mkQ] using h
    have h1 : (f : ↥A →* ↥Y).toAdditive = (g : ↥A →* ↥Y).toAdditive :=
      AddMonoidHom.toZModLinearMap_injective (n := 2)
        (M := Additive ↥A) (M₁ := Additive ↥Y) hL
    have h2 : (f : ↥A →* ↥Y) = (g : ↥A →* ↥Y) :=
      (MonoidHom.toAdditive (α := ↥A) (β := ↥Y)).injective h1
    exact Subtype.ext h2
  have hcardRange : Nat.card ↥F.range ≤ 2 ^ (k * k) := by
    haveI : Finite ((Additive ↥A) ⧸ W →ₗ[ZMod 2] Additive ↥Y) :=
      Nat.finite_of_card_ne_zero (by rw [hcardLM]; exact (pow_pos (by norm_num) _).ne')
    calc Nat.card ↥F.range ≤
          Nat.card ((Additive ↥A) ⧸ W →ₗ[ZMod 2] Additive ↥Y) :=
        Nat.card_le_card_of_injective Φ hΦinj
      _ = 2 ^ (k * k) := hcardLM
  have hP₁card := Subgroup.card_ker_mul_card_range F
  have hP₁bound : Nat.card ↥P₁ ≤
      Nat.card ↥(P ⊓ centralizer (A : Set G)) * 2 ^ (k * k) := by
    rw [← hP₁card, hFker]
    exact Nat.mul_le_mul_left _ hcardRange
  calc Nat.card P ≤ 2 ^ (k * (k - 1) / 2) * Nat.card ↥P₁ := hPbound
    _ ≤ 2 ^ (k * (k - 1) / 2) *
          (Nat.card ↥(P ⊓ centralizer (A : Set G)) * 2 ^ (k * k)) :=
        Nat.mul_le_mul_left _ hP₁bound
    _ = 2 ^ (k * (k - 1) / 2 + k * k) * Nat.card ↥(P ⊓ centralizer (A : Set G)) := by
        rw [pow_add]
        ring

end CFSG.GroupTheory
