module

public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR7

public section

namespace CFSG.GH74.GLS.Th2.Obs

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Th2
open scoped commutatorElement

section Action

variable {G : Type} [Group G]

@[expose] noncomputable def rhoL (L : Subgroup G) (g : G) : MulAut (kBar L) :=
  open scoped Classical in
  if h : g ∈ normalizer (L : Set G) then barAct L ⟨g, h⟩ else 1

theorem rhoL_of_mem {L : Subgroup G} {g : G} (h : g ∈ normalizer (L : Set G)) :
    rhoL L g = barAct L ⟨g, h⟩ := by simp [rhoL, h]

theorem rhoL_mul {L : Subgroup G} {g h : G} (hg : g ∈ normalizer (L : Set G))
    (hh : h ∈ normalizer (L : Set G)) : rhoL L (g * h) = rhoL L g * rhoL L h := by
  rw [rhoL_of_mem hg, rhoL_of_mem hh, rhoL_of_mem (mul_mem hg hh), ← map_mul]
  rfl

theorem rhoL_one (L : Subgroup G) : rhoL L 1 = 1 := by
  rw [rhoL_of_mem (one_mem _)]
  exact map_one _

theorem rhoL_inv {L : Subgroup G} {g : G} (hg : g ∈ normalizer (L : Set G)) :
    rhoL L g⁻¹ = (rhoL L g)⁻¹ := by
  rw [rhoL_of_mem hg, rhoL_of_mem (inv_mem hg), ← map_inv]
  rfl

theorem rhoL_mk {L : Subgroup G} {g : G} (hg : g ∈ normalizer (L : Set G)) (l : ↥L) :
    rhoL L g (QuotientGroup.mk l : kBar L) =
      QuotientGroup.mk ⟨g * l * g⁻¹, normalizer_conj_mem g hg l l.2⟩ := by
  rw [rhoL_of_mem hg]
  exact barAct_mk' L ⟨g, hg⟩ l

theorem rhoL_eq_one_iff {L : Subgroup G} {g : G} (hg : g ∈ normalizer (L : Set G)) :
    rhoL L g = 1 ↔ g ∈ centralizerSection L (pPrimeCoreOf 2 L) := by
  rw [rhoL_of_mem hg]
  exact barAct_eq_one_iff ⟨g, hg⟩

theorem rhoL_of_mem_L {L : Subgroup G} {k : G} (hk : k ∈ L) :
    rhoL L k = MulAut.conj (QuotientGroup.mk (⟨k, hk⟩ : ↥L) : kBar L) := by
  rw [rhoL_of_mem (Subgroup.le_normalizer hk)]
  exact barAct_of_mem hk


theorem isElementaryAbelian_sup_zpowers {E : Subgroup G} (hEel : CFSG.IsElementaryAbelian 2 ↥E)
    {u : G} (hu : u * u = 1) (hc : ∀ f ∈ E, f * u = u * f) :
    CFSG.IsElementaryAbelian 2 ↥(E ⊔ zpowers u) := by
  obtain ⟨hEc, hEsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hEel
  have hzp : ∀ w ∈ zpowers u, ∀ f ∈ E, w * f = f * w := by
    intro w hw f hf
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
    exact (Commute.zpow_left (show Commute u f from (hc f hf).symm) k).eq
  have hzz : ∀ a ∈ zpowers u, ∀ b ∈ zpowers u, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    rw [← zpow_add, ← zpow_add, add_comm]
  have hzsq : ∀ a ∈ zpowers u, a * a = 1 := by
    intro a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    have hu2' : u ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hu
    rw [← zpow_add, ← two_mul, zpow_mul, hu2', one_zpow]
  have hAB : ∀ a ∈ E, ∀ b ∈ zpowers u, a * b = b * a := fun x hx y hy => (hzp y hy x hx).symm
  apply C3.Layer1.Back.isElementaryAbelian_of_forall
  · intro a ha b hb
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := exists_mul_of_mem_sup_of_commute hAB ha
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := exists_mul_of_mem_sup_of_commute hAB hb
    have c11 : Commute a₁ b₁ := hEc a₁ ha₁ b₁ hb₁
    have c12 : Commute a₁ b₂ := hAB a₁ ha₁ b₂ hb₂
    have c21 : Commute a₂ b₁ := (hAB b₁ hb₁ a₂ ha₂).symm
    have c22 : Commute a₂ b₂ := hzz a₂ ha₂ b₂ hb₂
    exact (Commute.mul_left (Commute.mul_right c11 c12) (Commute.mul_right c21 c22)).eq
  · intro a ha
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := exists_mul_of_mem_sup_of_commute hAB ha
    have c12 : a₂ * a₁ = a₁ * a₂ := (hAB a₁ ha₁ a₂ ha₂).symm
    calc a₁ * a₂ * (a₁ * a₂) = a₁ * (a₂ * a₁) * a₂ := by group
      _ = a₁ * (a₁ * a₂) * a₂ := by rw [c12]
      _ = (a₁ * a₁) * (a₂ * a₂) := by group
      _ = 1 := by rw [hEsq a₁ ha₁, hzsq a₂ ha₂, one_mul]

section Finite

variable [Finite G]

theorem key_max {L E N : Subgroup G} {e e' : G} {u0 : kBar L}
    (hEel : CFSG.IsElementaryAbelian 2 ↥E) (hEL : ∀ x ∈ E, x ∈ normalizer (L : Set G))
    (he : e ∈ E) (he1 : e ≠ 1) (he' : e' ∈ E)
    (hEN : E ≤ N) (hNinv : ∀ c ∈ centralizer ({e} : Set G), ∀ n ∈ N, c * n * c⁻¹ ∈ N)
    (hmax : ∀ F : Subgroup G, E ≤ F → F ≤ N → CFSG.IsElementaryAbelian 2 ↥F → F = E)
    (hu2 : u0 ^ 2 = 1) (hu1 : u0 ≠ 1)
    (hu : u0 ∈ Subgroup.closure {x : kBar L | ∃ c ∈ fixedSubgroup (kBar L) (rhoL L e),
      x = rhoL L e' c * c⁻¹})
    (hfix : ∀ x ∈ E, rhoL L x u0 = u0)
    (hnot : ∀ x ∈ E, rhoL L x ≠ MulAut.conj u0) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hEc, hEsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hEel
  have he2 : orderOf e = 2 := orderOf_eq_prime (by rw [sq]; exact hEsq e he) he1
  have heN : e ∈ normalizer (L : Set G) := hEL e he
  set J : Subgroup G := L ⊓ centralizer ({e} : Set G) with hJ
  have hJE : ∀ x ∈ E, ∀ j ∈ J, x * j * x⁻¹ ∈ J := by
    intro x hx j hj
    refine ⟨normalizer_conj_mem x (hEL x hx) j hj.1, ?_⟩
    have hxe : x * e = e * x := hEc x hx e he
    have hje : j * e = e * j := mem_centralizer_singleton_iff.1 hj.2
    show x * j * x⁻¹ ∈ centralizer ({e} : Set G)
    rw [mem_centralizer_singleton_iff]
    calc x * j * x⁻¹ * e = x * j * (x⁻¹ * e) := by group
      _ = x * j * (e * x⁻¹) := by
        congr 1
        calc x⁻¹ * e = x⁻¹ * (e * x) * x⁻¹ := by group
          _ = x⁻¹ * (x * e) * x⁻¹ := by rw [hxe]
          _ = e * x⁻¹ := by group
      _ = x * (j * e) * x⁻¹ := by group
      _ = x * (e * j) * x⁻¹ := by rw [hje]
      _ = e * (x * j * x⁻¹) := by
        calc x * (e * j) * x⁻¹ = (x * e) * j * x⁻¹ := by group
          _ = (e * x) * j * x⁻¹ := by rw [hxe]
          _ = e * (x * j * x⁻¹) := by group
  set S : Set G := {y | ∃ j ∈ J, y = e' * j * e'⁻¹ * j⁻¹} with hS
  set J₁ : Subgroup G := Subgroup.closure S with hJ₁
  have hSJ : S ⊆ (J : Set G) := by
    rintro y ⟨j, hj, rfl⟩
    exact J.mul_mem (hJE e' he' j hj) (J.inv_mem hj)
  have hJ₁J : J₁ ≤ J := (Subgroup.closure_le J).2 hSJ
  have hSN : S ⊆ (N : Set G) := by
    rintro y ⟨j, hj, rfl⟩
    have h1 : e' * j * e'⁻¹ * j⁻¹ = e' * (j * e'⁻¹ * j⁻¹) := by group
    rw [h1]
    exact N.mul_mem (hEN he') (hNinv j hj.2 e'⁻¹ (hEN (E.inv_mem he')))
  have hJ₁N : J₁ ≤ N := (Subgroup.closure_le N).2 hSN
  have hJ₁E : ∀ x ∈ E, ∀ y ∈ J₁, x * y * x⁻¹ ∈ J₁ := by
    intro x hx y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨j, hj, rfl⟩ := hy
      apply Subgroup.subset_closure
      refine ⟨x * j * x⁻¹, hJE x hx j hj, ?_⟩
      have hxe' : x * e' = e' * x := hEc x hx e' he'
      have hxe'' : x * e'⁻¹ = e'⁻¹ * x := by
        calc x * e'⁻¹ = e'⁻¹ * (e' * x) * e'⁻¹ := by group
          _ = e'⁻¹ * (x * e') * e'⁻¹ := by rw [hxe']
          _ = e'⁻¹ * x := by group
      calc x * (e' * j * e'⁻¹ * j⁻¹) * x⁻¹
          = (x * e') * j * (e'⁻¹ * j⁻¹) * x⁻¹ := by group
        _ = (e' * x) * j * (e'⁻¹ * j⁻¹) * x⁻¹ := by rw [hxe']
        _ = e' * (x * j * x⁻¹) * (x * (e'⁻¹ * j⁻¹) * x⁻¹) := by group
        _ = e' * (x * j * x⁻¹) * ((x * e'⁻¹) * j⁻¹ * x⁻¹) := by group
        _ = e' * (x * j * x⁻¹) * ((e'⁻¹ * x) * j⁻¹ * x⁻¹) := by rw [hxe'']
        _ = e' * (x * j * x⁻¹) * e'⁻¹ * (x * j * x⁻¹)⁻¹ := by group
    | one => simp
    | mul a b _ _ iha ihb =>
      have : x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := by group
      rw [this]
      exact J₁.mul_mem iha ihb
    | inv a _ iha =>
      have : x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ := by group
      rw [this]
      exact J₁.inv_mem iha
  let π : ↥L →* kBar L := QuotientGroup.mk' (pPrimeCore 2 ↥L)
  let S' : Subgroup (kBar L) := (J₁.subgroupOf L).map π
  have hu_in : u0 ∈ S' := by
    have hgen : {x : kBar L | ∃ c ∈ fixedSubgroup (kBar L) (rhoL L e),
        x = rhoL L e' c * c⁻¹} ⊆ (S' : Set (kBar L)) := by
      rintro x ⟨c, hc, rfl⟩
      have hc' : barAct L ⟨e, heN⟩ c = c := by
        have h1 : rhoL L e c = c := hc
        rwa [rhoL_of_mem heN] at h1
      obtain ⟨l, hl, hle, hlc⟩ := exists_mem_cent_lift he2 heN hc'
      have hlJ : l ∈ J := ⟨hl, mem_centralizer_singleton_iff.2 hle⟩
      have hgenJ : e' * l * e'⁻¹ * l⁻¹ ∈ J₁ := Subgroup.subset_closure ⟨l, hlJ, rfl⟩
      have hgenL : e' * l * e'⁻¹ * l⁻¹ ∈ L := (hJ₁J hgenJ).1
      refine ⟨⟨e' * l * e'⁻¹ * l⁻¹, hgenL⟩, Subgroup.mem_subgroupOf.2 hgenJ, ?_⟩
      show (QuotientGroup.mk ⟨e' * l * e'⁻¹ * l⁻¹, hgenL⟩ : kBar L) = rhoL L e' c * c⁻¹
      rw [← hlc, rhoL_mk (hEL e' he') ⟨l, hl⟩, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      congr 1
    exact Subgroup.closure_le S' |>.2 hgen hu
  obtain ⟨⟨j₁, hj₁L⟩, hj₁J₁, hj₁u⟩ := hu_in
  have hj₁J₁' : j₁ ∈ J₁ := Subgroup.mem_subgroupOf.1 hj₁J₁
  set O₁ : Subgroup G := J₁ ⊓ pPrimeCoreOf 2 L with hO₁
  have hO₁odd : ¬ 2 ∣ Nat.card O₁ := by
    have h1 : Nat.card O₁ ∣ Nat.card (pPrimeCoreOf 2 L) := Subgroup.card_dvd_of_le inf_le_right
    have h2 : ¬ 2 ∣ Nat.card (pPrimeCoreOf 2 L) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 (coprime_card_pPrimeCoreOf L)
    exact fun h => h2 (h.trans h1)
  have hO₁E : ∀ f ∈ E, ∀ o ∈ O₁, f * o * f⁻¹ ∈ O₁ := fun f hf o ho =>
    ⟨hJ₁E f hf o ho.1, (Subgroup.mem_normalizer_iff.1
      (TwoThin.mem_normalizer_pPrimeCoreOf (hEL f hf)) o).1 ho.2⟩
  have hEp : IsPGroup 2 ↥E := CFSG.IsElementaryAbelian.isPGroup 2 ↥E
  have hk : ∀ f ∈ E, j₁⁻¹ * (f * j₁ * f⁻¹) ∈ O₁ := by
    intro f hf
    have hfN := hEL f hf
    have hmem : j₁⁻¹ * (f * j₁ * f⁻¹) ∈ J₁ :=
      J₁.mul_mem (J₁.inv_mem hj₁J₁') (hJ₁E f hf j₁ hj₁J₁')
    refine ⟨hmem, ?_⟩
    have hLmem : j₁⁻¹ * (f * j₁ * f⁻¹) ∈ L :=
      L.mul_mem (L.inv_mem hj₁L) (normalizer_conj_mem f hfN j₁ hj₁L)
    refine C3.Layer1.Back.Setup91.mem_pPrimeCoreOf_iff.2 ⟨hLmem, ?_⟩
    have h1 : (QuotientGroup.mk ⟨f * j₁ * f⁻¹, normalizer_conj_mem f hfN j₁ hj₁L⟩ : kBar L) =
        QuotientGroup.mk ⟨j₁, hj₁L⟩ := by
      rw [← rhoL_mk hfN ⟨j₁, hj₁L⟩]
      have h0 : (QuotientGroup.mk ⟨j₁, hj₁L⟩ : kBar L) = u0 := hj₁u
      rw [h0, hfix f hf]
    have h2 := QuotientGroup.eq.1 h1.symm
    have h3 : (⟨j₁⁻¹ * (f * j₁ * f⁻¹), hLmem⟩ : ↥L) =
        (⟨j₁, hj₁L⟩ : ↥L)⁻¹ * ⟨f * j₁ * f⁻¹, normalizer_conj_mem f hfN j₁ hj₁L⟩ :=
      Subtype.ext (by simp)
    rw [h3]
    exact h2
  obtain ⟨o, ho, hofix⟩ := Th2.L83.exists_fixed_mem_coset hO₁odd hEp hO₁E hk
  set j₂ : G := j₁ * o with hj₂
  have hoJ₁ : o ∈ J₁ := ho.1
  have hoO : o ∈ pPrimeCoreOf 2 L := ho.2
  have hj₂J₁ : j₂ ∈ J₁ := J₁.mul_mem hj₁J₁' hoJ₁
  have hj₂L : j₂ ∈ L := L.mul_mem hj₁L (TwoThin.pPrimeCoreOf_le L hoO)
  have hj₂c : ∀ f ∈ E, f * j₂ * f⁻¹ = j₂ := hofix
  have hπ : (QuotientGroup.mk ⟨j₂, hj₂L⟩ : kBar L) = u0 := by
    have h0 : (QuotientGroup.mk ⟨j₁, hj₁L⟩ : kBar L) = u0 := hj₁u
    obtain ⟨hoL, hom⟩ := C3.Layer1.Back.Setup91.mem_pPrimeCoreOf_iff.1 hoO
    have h1 : (⟨j₂, hj₂L⟩ : ↥L) = ⟨j₁, hj₁L⟩ * ⟨o, hoL⟩ := rfl
    rw [h1, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 hom, mul_one, h0]
  have hOd : Nat.card (pPrimeCoreOf 2 L) ≠ 0 := Nat.card_pos.ne'
  have hsqO : j₂ ^ 2 ∈ pPrimeCoreOf 2 L := by
    refine C3.Layer1.Back.Setup91.mem_pPrimeCoreOf_iff.2 ⟨L.pow_mem hj₂L 2, ?_⟩
    apply (QuotientGroup.eq_one_iff _).1
    have : (QuotientGroup.mk (⟨j₂ ^ 2, L.pow_mem hj₂L 2⟩ : ↥L) : kBar L) =
        (QuotientGroup.mk (⟨j₂, hj₂L⟩ : ↥L) : kBar L) ^ 2 := by
      rw [← QuotientGroup.mk_pow]; rfl
    rw [this, hπ, hu2]
  have hsqodd : Odd (orderOf (j₂ ^ 2)) := by
    have h1 := Subgroup.orderOf_dvd_natCard (pPrimeCoreOf 2 L) hsqO
    exact Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd L) h1
  have hord2 : orderOf u0 = 2 := orderOf_eq_prime (by rw [sq] at hu2 ⊢; exact hu2) hu1
  have hneven : Even (orderOf j₂) := by
    by_contra hne
    have hodd : Odd (orderOf j₂) := Nat.not_even_iff_odd.1 hne
    have h1 : orderOf (QuotientGroup.mk (⟨j₂, hj₂L⟩ : ↥L) : kBar L) ∣ orderOf (⟨j₂, hj₂L⟩ : ↥L) :=
      orderOf_map_dvd (QuotientGroup.mk' (pPrimeCore 2 ↥L)) _
    have h2 : orderOf (⟨j₂, hj₂L⟩ : ↥L) = orderOf j₂ := Subgroup.orderOf_mk _ _
    rw [hπ, hord2, h2] at h1
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h1)
  obtain ⟨m, hm⟩ := hneven
  have hm2 : orderOf j₂ = 2 * m := by omega
  have hmodd : Odd m := by
    have h1 : orderOf (j₂ ^ 2) = orderOf j₂ / Nat.gcd (orderOf j₂) 2 := orderOf_pow' _ (by norm_num)
    have h2 : Nat.gcd (orderOf j₂) 2 = 2 := by rw [hm2]; simp
    rw [h1, h2, hm2] at hsqodd
    simpa using hsqodd
  set u : G := j₂ ^ m with hu_def
  have hmpos : 0 < m := by
    have : 0 < orderOf j₂ := orderOf_pos _
    omega
  have hu_sq : u * u = 1 := by
    rw [hu_def, ← pow_add, ← two_mul, ← hm2]
    exact pow_orderOf_eq_one _
  have huJ₁ : u ∈ J₁ := J₁.pow_mem hj₂J₁ m
  have huL : u ∈ L := L.pow_mem hj₂L m
  have huc : ∀ f ∈ E, f * u * f⁻¹ = u := by
    intro f hf
    rw [hu_def]
    have : f * j₂ ^ m * f⁻¹ = (f * j₂ * f⁻¹) ^ m := conj_pow.symm
    rw [this, hj₂c f hf]
  have hu_cl : (QuotientGroup.mk (⟨u, huL⟩ : ↥L) : kBar L) = u0 := by
    have : (QuotientGroup.mk (⟨u, huL⟩ : ↥L) : kBar L) =
        (QuotientGroup.mk (⟨j₂, hj₂L⟩ : ↥L) : kBar L) ^ m := by
      rw [← QuotientGroup.mk_pow]; rfl
    rw [this, hπ]
    obtain ⟨k, hk'⟩ := hmodd
    rw [hk', pow_succ, pow_mul, hu2, one_pow, one_mul]
  have huE_comm : ∀ f ∈ E, f * u = u * f := by
    intro f hf
    have := huc f hf
    calc f * u = f * u * f⁻¹ * f := by group
      _ = u * f := by rw [this]
  have hF : CFSG.IsElementaryAbelian 2 ↥(E ⊔ zpowers u) :=
    isElementaryAbelian_sup_zpowers hEel hu_sq huE_comm
  have hFN : E ⊔ zpowers u ≤ N := sup_le hEN (Subgroup.zpowers_le.2 (hJ₁N huJ₁))
  have hFE : E ⊔ zpowers u = E := hmax _ le_sup_left hFN hF
  have huE : u ∈ E := by
    have : u ∈ E ⊔ zpowers u := Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
    rwa [hFE] at this
  apply hnot u huE
  rw [rhoL_of_mem_L huL, hu_cl]


end Finite

end Action

section Aux

variable {G : Type} [Group G]

theorem mem_four_of_card [Finite G] {E : Subgroup G} (hcard : Nat.card E = 4) {a b : G} (ha : a ∈ E)
    (hb : b ∈ E) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) (hsa : a * a = 1) :
    ∀ x ∈ E, x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  classical
  have hab1 : a * b ≠ 1 := by
    intro h
    apply hab
    have h1 : b = a⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [h1]
    exact (inv_eq_of_mul_eq_one_right hsa).symm
  have hab2 : a * b ≠ a := fun h => hb1 (mul_eq_left.1 h)
  have hab3 : a * b ≠ b := fun h => ha1 (mul_eq_right.1 h)
  have hmem : ({1, a, b, a * b} : Set G) ⊆ (E : Set G) := by
    intro y hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact E.one_mem
    · exact ha
    · exact hb
    · exact E.mul_mem ha hb
  have hncard : ({1, a, b, a * b} : Set G).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair (Ne.symm hab3)]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hab, Ne.symm hab2⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨Ne.symm ha1, Ne.symm hb1, Ne.symm hab1⟩
  have hE : (E : Set G).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact hcard
  have heq := Set.eq_of_subset_of_ncard_le hmem (by rw [hncard, hE]) (Set.toFinite _)
  intro x hx
  have : x ∈ ({1, a, b, a * b} : Set G) := by rw [heq]; exact hx
  simpa using this

theorem exists_third {E : Subgroup G} [Finite G] (hcard : Nat.card E = 4) {e : G}
    (he2 : orderOf e = 2) : ∃ e' ∈ E, e' ≠ 1 ∧ e' ≠ e := by
  by_contra hno
  push Not at hno
  have hle : E ≤ zpowers e := by
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1]; exact one_mem _
    · rw [hno x hx hx1]; exact Subgroup.mem_zpowers e
  have h1 := Subgroup.card_le_of_le hle
  rw [Nat.card_zpowers, he2, hcard] at h1
  omega


section Dihedral

theorem dihedral_central {k : ℕ} [NeZero k] (hk : 4 ≤ k) (hk2 : Even k) {d : DihedralGroup k}
    (hd : ∀ x : DihedralGroup k, d * x = x * d) :
    d = 1 ∨ d = DihedralGroup.r ((k / 2 : ℕ) : ZMod k) := by
  have hc : d ∈ Subgroup.center (DihedralGroup k) :=
    Subgroup.mem_center_iff.2 (fun g => (hd g).symm)
  rw [DihedralGroup.center_eq_closure_of_even_ne_two hk2 (by omega)] at hc
  have h2 : orderOf (DihedralGroup.r ((k / 2 : ℕ) : ZMod k)) = 2 := by
    rw [DihedralGroup.orderOf_r]
    obtain ⟨m, hm⟩ := hk2
    have hm0 : 0 < m := by omega
    have hdiv : k / 2 = m := by omega
    rw [hdiv, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega), hm]
    have : Nat.gcd (m + m) m = m := Nat.gcd_eq_right ⟨2, by ring⟩
    rw [this]
    exact Nat.div_eq_of_eq_mul_left hm0 (by ring)
  exact mem_zpowers_two h2 hc

theorem central_of_dihedral {P : Subgroup G} {n : ℕ} (hn : 3 ≤ n)
    (φ : ↥P ≃* DihedralGroup (2 ^ (n - 1))) {z : G} (hzP : z ∈ P) (hz2 : orderOf z = 2)
    (hzc : ∀ p ∈ P, z * p = p * z) :
    (∀ u ∈ P, (∀ p ∈ P, u * p = p * u) → u = 1 ∨ u = z) ∧
      ∃ w ∈ P, w * w = 1 ∧ w ≠ 1 ∧ w ≠ z := by
  have hk4 : 4 ≤ 2 ^ (n - 1) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hkev : Even (2 ^ (n - 1)) := (Nat.even_pow.2 ⟨even_two, by omega⟩)
  have : NeZero (2 ^ (n - 1)) := ⟨by positivity⟩
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz2
    omega
  have hcen : ∀ u : ↥P, (∀ p : ↥P, u * p = p * u) →
      φ u = 1 ∨ φ u = DihedralGroup.r (((2 ^ (n - 1)) / 2 : ℕ) : ZMod (2 ^ (n - 1))) := by
    intro u hu
    apply dihedral_central hk4 hkev
    intro x
    obtain ⟨p, rfl⟩ := φ.surjective x
    rw [← map_mul, ← map_mul, hu p]
  have hz' : φ ⟨z, hzP⟩ = DihedralGroup.r (((2 ^ (n - 1)) / 2 : ℕ) : ZMod (2 ^ (n - 1))) := by
    rcases hcen ⟨z, hzP⟩ (fun p => Subtype.ext (hzc p p.2)) with h | h
    · exfalso
      have : (⟨z, hzP⟩ : ↥P) = 1 := φ.injective (by rw [h, map_one])
      exact hz1 (congrArg Subtype.val this)
    · exact h
  refine ⟨?_, ?_⟩
  · intro u hu hcu
    rcases hcen ⟨u, hu⟩ (fun p => Subtype.ext (hcu p p.2)) with h | h
    · left
      have : (⟨u, hu⟩ : ↥P) = 1 := φ.injective (by rw [h, map_one])
      exact congrArg Subtype.val this
    · right
      have : (⟨u, hu⟩ : ↥P) = ⟨z, hzP⟩ := φ.injective (by rw [h, hz'])
      exact congrArg Subtype.val this
  · refine ⟨(φ.symm (DihedralGroup.sr 0)).1, (φ.symm (DihedralGroup.sr 0)).2, ?_, ?_, ?_⟩
    · have : φ.symm (DihedralGroup.sr 0) * φ.symm (DihedralGroup.sr 0) = 1 := by
        rw [← map_mul, DihedralGroup.sr_mul_self, map_one]
      exact congrArg Subtype.val this
    · intro h
      have h1 : φ.symm (DihedralGroup.sr 0) = 1 := Subtype.ext (by simpa using h)
      have h2 : DihedralGroup.sr (0 : ZMod (2 ^ (n - 1))) = 1 := by
        rw [← map_one φ.symm] at h1
        exact φ.symm.injective h1
      rw [DihedralGroup.one_def] at h2
      cases h2
    · intro h
      have h1 : φ.symm (DihedralGroup.sr 0) = ⟨z, hzP⟩ := Subtype.ext h
      have h2 : DihedralGroup.sr (0 : ZMod (2 ^ (n - 1))) = φ ⟨z, hzP⟩ := by
        rw [← h1]; simp
      rw [hz'] at h2
      cases h2

end Dihedral


section Injective

variable [Finite G]

theorem rhoL_eq_one_of_mem_P {L P : Subgroup G} {n : ℕ} (hn : 3 ≤ n)
    (φ : ↥P ≃* DihedralGroup (2 ^ (n - 1))) (hPn : ∀ p ∈ P, p ∈ normalizer (L : Set G))
    {z : G} (hzP : z ∈ P) (hz2 : orderOf z = 2) (hzc : ∀ p ∈ P, z * p = p * z)
    (hz : rhoL L z ≠ 1) : ∀ p ∈ P, rhoL L p = 1 → p = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcen, -⟩ := central_of_dihedral hn φ hzP hz2 hzc
  let ρP : ↥P →* MulAut (kBar L) := (barAct L).comp (Subgroup.inclusion (fun p hp => hPn p hp))
  have hρP : ∀ p : ↥P, ρP p = rhoL L p := fun p => (rhoL_of_mem (hPn p p.2)).symm
  have hPp : IsPGroup 2 ↥P := by
    have : NeZero (2 ^ (n - 1)) := ⟨by positivity⟩
    have hcard : Nat.card ↥P = 2 ^ n := by
      rw [Nat.card_congr φ.toEquiv, DihedralGroup.nat_card, ← pow_succ']
      congr 1
      omega
    exact IsPGroup.of_card hcard
  have hnil : Group.IsNilpotent ↥P := hPp.isNilpotent
  intro p hp hp1
  by_contra hne
  have hker : ρP.ker ≠ ⊥ := by
    intro h
    have hmem : (⟨p, hp⟩ : ↥P) ∈ ρP.ker := by
      rw [MonoidHom.mem_ker, hρP]
      exact hp1
    rw [h, Subgroup.mem_bot] at hmem
    exact hne (congrArg Subtype.val hmem)
  have hmeet := Group.IsNilpotent.inf_center_ne_bot_of_normal hker
  obtain ⟨⟨w, hw⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hmeet
  have hwc : ∀ q ∈ P, w.1 * q = q * w.1 := by
    intro q hq
    have := Subgroup.mem_center_iff.1 hw.2 ⟨q, hq⟩
    exact (congrArg Subtype.val this).symm
  rcases hcen w.1 w.2 hwc with h | h
  · apply hw1
    apply Subtype.ext
    apply Subtype.ext
    exact h
  · have hwz : w = ⟨z, hzP⟩ := Subtype.ext h
    apply hz
    rw [← hρP ⟨z, hzP⟩, ← hwz]
    exact hw.1

theorem rhoL_injOn_P {L P : Subgroup G} {n : ℕ} (hn : 3 ≤ n)
    (φ : ↥P ≃* DihedralGroup (2 ^ (n - 1))) (hPn : ∀ p ∈ P, p ∈ normalizer (L : Set G))
    {z : G} (hzP : z ∈ P) (hz2 : orderOf z = 2) (hzc : ∀ p ∈ P, z * p = p * z)
    (hz : rhoL L z ≠ 1) {p q : G} (hp : p ∈ P) (hq : q ∈ P) (h : rhoL L p = rhoL L q) : p = q := by
  have h1 : rhoL L (p * q⁻¹) = 1 := by
    rw [rhoL_mul (hPn p hp) (inv_mem (hPn q hq)), rhoL_inv (hPn q hq), h, mul_inv_cancel]
  have := rhoL_eq_one_of_mem_P hn φ hPn hzP hz2 hzc hz (p * q⁻¹) (P.mul_mem hp (P.inv_mem hq)) h1
  exact mul_inv_eq_one.1 this

end Injective

end Aux

end CFSG.GH74.GLS.Th2.Obs
