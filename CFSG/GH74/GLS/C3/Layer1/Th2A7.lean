module

public import CFSG.GH74.GLS.C3.Layer1.Th2Shape
public import CFSG.GH74.GLS.C3.Layer1.Thm1AutA7
public import CFSG.GH74.GLS.C3.Layer1.Back91Setup

public section

namespace CFSG.GH74.GLS.Th2

open Subgroup CFSG.ABGLocalTools Equiv

namespace A7Aux

theorem isElementaryAbelian_two_of {X : Type*} [Group X] {E : Subgroup X}
    (hc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hsq : ∀ a ∈ E, a * a = 1) :
    IsElementaryAbelian 2 ↥E := by
  have : IsMulCommutative ↥E := ⟨⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩⟩
  refine ⟨?_⟩
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x => ?_
  apply Subtype.ext
  simpa [pow_two] using hsq x x.2

theorem sq_of_isElementaryAbelian {X : Type*} [Group X] {E : Subgroup X}
    (hE : IsElementaryAbelian 2 ↥E) : ∀ a ∈ E, a * a = 1 := by
  intro a ha
  have := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := E) a ha
  rwa [pow_two] at this

theorem comm_of_isElementaryAbelian {X : Type*} [Group X] {E : Subgroup X}
    (hE : IsElementaryAbelian 2 ↥E) : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
  intro a ha b hb
  exact congrArg Subtype.val (hE.toIsMulCommutative.is_comm.comm (⟨a, ha⟩ : E) ⟨b, hb⟩)

@[expose] def modP0 : Subgroup (Perm (Fin 7)) := IVK.A7.T0 ⊓ alternatingGroup (Fin 7)

theorem mem_modP0_iff {x : Perm (Fin 7)} : x ∈ modP0 ↔ x ∈ IVK.A7.P0list := by
  have h := Set.ext_iff.1 IVK.A7.T0_inf_A7_coe x
  rw [SetLike.mem_coe, Finset.mem_coe, List.mem_toFinset] at h
  exact h

theorem mem_P0list_iff {x : Perm (Fin 7)} : x ∈ IVK.A7.P0list ↔
    x = 1 ∨ x = IVK.A7.r ^ 2 ∨ x = IVK.A7.s * IVK.A7.r ∨ x = IVK.A7.s * IVK.A7.r ^ 3 ∨
      x = IVK.A7.r * IVK.A7.f0 ∨ x = IVK.A7.r ^ 3 * IVK.A7.f0 ∨ x = IVK.A7.s * IVK.A7.f0 ∨
      x = IVK.A7.s * IVK.A7.r ^ 2 * IVK.A7.f0 :=
  IVK.A7.mem_P0list_iff

@[expose] def Vlist : List (Perm (Fin 7)) :=
  [1, IVK.A7.r ^ 2, IVK.A7.s * IVK.A7.r, IVK.A7.r ^ 2 * (IVK.A7.s * IVK.A7.r)]

@[expose] def Wlist : List (Perm (Fin 7)) :=
  [1, IVK.A7.r ^ 2, IVK.A7.s * IVK.A7.f0, IVK.A7.r ^ 2 * (IVK.A7.s * IVK.A7.f0)]

theorem mem_Vsub_iff {x : Perm (Fin 7)} : x ∈ IVK.A7.Vsub ↔ x ∈ Vlist := by
  show x ∈ IVK.A7.klein _ _ _ _ _ ↔ _
  rw [IVK.A7.mem_klein]
  simp [Vlist]

theorem mem_Wsub_iff {x : Perm (Fin 7)} : x ∈ IVK.A7.Wsub ↔ x ∈ Wlist := by
  show x ∈ IVK.A7.klein _ _ _ _ _ ↔ _
  rw [IVK.A7.mem_klein]
  simp [Wlist]

theorem Vsub_le_P0 : IVK.A7.Vsub ≤ modP0 := by
  intro x hx
  rw [mem_Vsub_iff] at hx
  rw [mem_modP0_iff, mem_P0list_iff]
  simp only [Vlist, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> decide

theorem Wsub_le_P0 : IVK.A7.Wsub ≤ modP0 := by
  intro x hx
  rw [mem_Wsub_iff] at hx
  rw [mem_modP0_iff, mem_P0list_iff]
  simp only [Wlist, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> decide

theorem card_Vsub : Nat.card IVK.A7.Vsub = 4 :=
  IVK.A7.card_klein _ _ _ (by decide) (by decide) (by decide)

theorem card_Wsub : Nat.card IVK.A7.Wsub = 4 :=
  IVK.A7.card_klein _ _ _ (by decide) (by decide) (by decide)

theorem sq_Vsub : ∀ x ∈ IVK.A7.Vsub, x * x = 1 := by
  intro x hx
  rw [mem_Vsub_iff] at hx
  simp only [Vlist, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> decide

theorem comm_Vsub : ∀ x ∈ IVK.A7.Vsub, ∀ y ∈ IVK.A7.Vsub, x * y = y * x := by
  intro x hx y hy
  rw [mem_Vsub_iff] at hx hy
  simp only [Vlist, List.mem_cons, List.not_mem_nil, or_false] at hx hy
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;> decide

theorem sq_Wsub : ∀ x ∈ IVK.A7.Wsub, x * x = 1 := by
  intro x hx
  rw [mem_Wsub_iff] at hx
  simp only [Wlist, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> decide

theorem comm_Wsub : ∀ x ∈ IVK.A7.Wsub, ∀ y ∈ IVK.A7.Wsub, x * y = y * x := by
  intro x hx y hy
  rw [mem_Wsub_iff] at hx hy
  simp only [Wlist, List.mem_cons, List.not_mem_nil, or_false] at hx hy
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;> decide

theorem inv_mem_VW : ∀ x ∈ IVK.A7.P0list, x * x = 1 → x ∈ IVK.A7.Vsub ∨ x ∈ IVK.A7.Wsub := by
  intro x hx
  simp only [mem_Vsub_iff, mem_Wsub_iff]
  rcases mem_P0list_iff.1 hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem no_mixed : ∀ x ∈ IVK.A7.P0list, ∀ y ∈ IVK.A7.P0list, x ∈ IVK.A7.Wsub → x ∉ IVK.A7.Vsub →
    y ∈ IVK.A7.Vsub → y ∉ IVK.A7.Wsub → x * y ≠ y * x := by
  intro x hx y hy
  simp only [mem_Vsub_iff, mem_Wsub_iff]
  rcases mem_P0list_iff.1 hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases mem_P0list_iff.1 hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem centralizer_W :
    ∀ x ∈ IVK.A7.P0list, (∀ w ∈ IVK.A7.Wsub, x * w = w * x) → x ∈ IVK.A7.Wsub := by
  intro x hx h
  have h1 := h (IVK.A7.s * IVK.A7.f0) (by rw [mem_Wsub_iff]; decide)
  rw [mem_Wsub_iff]
  revert h1
  rcases mem_P0list_iff.1 hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem rsq_mem_V : IVK.A7.r ^ 2 ∈ IVK.A7.Vsub := by rw [mem_Vsub_iff]; decide

theorem rsq_mem_W : IVK.A7.r ^ 2 ∈ IVK.A7.Wsub := by rw [mem_Wsub_iff]; decide

theorem orderOf_rsq : orderOf (IVK.A7.r ^ 2 : Perm (Fin 7)) = 2 :=
  orderOf_eq_prime IVK.A7.rsq_sq IVK.A7.rsq_ne_one

theorem le_V_or_le_W (E : Subgroup (Perm (Fin 7))) (hE : E ≤ modP0) (hsq : ∀ x ∈ E, x * x = 1)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) : E ≤ IVK.A7.Vsub ∨ E ≤ IVK.A7.Wsub := by
  have hmem : ∀ x ∈ E, x ∈ IVK.A7.Vsub ∨ x ∈ IVK.A7.Wsub := fun x hx =>
    inv_mem_VW x (mem_modP0_iff.1 (hE hx)) (hsq x hx)
  by_cases hV : ∀ x ∈ E, x ∈ IVK.A7.Vsub
  · exact Or.inl hV
  · right
    push Not at hV
    obtain ⟨x, hxE, hxV⟩ := hV
    have hxW : x ∈ IVK.A7.Wsub := (hmem x hxE).resolve_left hxV
    intro y hy
    by_contra hyW
    have hyV : y ∈ IVK.A7.Vsub := (hmem y hy).resolve_right hyW
    exact no_mixed x (mem_modP0_iff.1 (hE hxE)) y (mem_modP0_iff.1 (hE hy)) hxW hxV hyV hyW
      (hcomm x hxE y hy)

@[expose] def moved (V : Subgroup (Perm (Fin 7))) : Set (Fin 7) := {i | ∃ x ∈ V, x i ≠ i}

theorem moved_V : (moved IVK.A7.Vsub).ncard = 4 := by
  have : moved IVK.A7.Vsub =
      ↑(Finset.univ.filter (fun i : Fin 7 => ∃ x ∈ Vlist, x i ≠ i)) := by
    ext i; simp [moved, mem_Vsub_iff]
  rw [this, Set.ncard_coe_finset]
  decide

theorem moved_W : (moved IVK.A7.Wsub).ncard = 6 := by
  have : moved IVK.A7.Wsub =
      ↑(Finset.univ.filter (fun i : Fin 7 => ∃ x ∈ Wlist, x i ≠ i)) := by
    ext i; simp [moved, mem_Wsub_iff]
  rw [this, Set.ncard_coe_finset]
  decide

theorem conj_ne_iff (g σ : Perm (Fin 7)) (i : Fin 7) :
    (g * σ * g⁻¹) i ≠ i ↔ σ (g⁻¹ i) ≠ g⁻¹ i := by
  rw [Perm.mul_apply, Perm.mul_apply]
  constructor
  · intro h h'
    exact h (by rw [h']; simp)
  · intro h h'
    apply h
    have := congrArg (fun a => g⁻¹ a) h'
    simpa using this

theorem conj_ne_iff' (g σ : Perm (Fin 7)) (i : Fin 7) :
    (g⁻¹ * σ * g) i ≠ i ↔ σ (g i) ≠ g i := by
  have := conj_ne_iff g⁻¹ σ i
  rwa [inv_inv] at this

section Transfer

variable {G : Type} [Group G] {P : Subgroup G}

@[expose] def pull (θ : ↥P →* Perm (Fin 7)) (V : Subgroup (Perm (Fin 7))) : Subgroup G :=
  (V.comap θ).map P.subtype

theorem mem_pull {θ : ↥P →* Perm (Fin 7)} {V : Subgroup (Perm (Fin 7))} {x : G} :
    x ∈ pull θ V ↔ ∃ hx : x ∈ P, θ ⟨x, hx⟩ ∈ V := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem pull_le (θ : ↥P →* Perm (Fin 7)) (V : Subgroup (Perm (Fin 7))) : pull θ V ≤ P := by
  intro x hx
  exact (mem_pull.1 hx).1

theorem pull_mono {θ : ↥P →* Perm (Fin 7)} {V W : Subgroup (Perm (Fin 7))} (h : V ≤ W) :
    pull θ V ≤ pull θ W := by
  intro x hx
  obtain ⟨hxP, hxV⟩ := mem_pull.1 hx
  exact mem_pull.2 ⟨hxP, h hxV⟩

theorem card_pull {θ : ↥P →* Perm (Fin 7)} (hθ : Function.Injective θ)
    {V : Subgroup (Perm (Fin 7))} (hV : V ≤ θ.range) : Nat.card ↥(pull θ V) = Nat.card ↥V := by
  unfold pull
  rw [Subgroup.card_map_of_injective P.subtype_injective]
  conv_rhs => rw [← Subgroup.map_comap_eq_self hV]
  exact (Subgroup.card_map_of_injective hθ).symm

theorem isElementaryAbelian_pull {θ : ↥P →* Perm (Fin 7)} (hθ : Function.Injective θ)
    {V : Subgroup (Perm (Fin 7))} (hc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hsq : ∀ x ∈ V, x * x = 1) :
    IsElementaryAbelian 2 ↥(pull θ V) := by
  refine isElementaryAbelian_two_of ?_ ?_
  · intro a ha b hb
    obtain ⟨haP, ha'⟩ := mem_pull.1 ha
    obtain ⟨hbP, hb'⟩ := mem_pull.1 hb
    have h := hc _ ha' _ hb'
    have : (⟨a, haP⟩ : ↥P) * ⟨b, hbP⟩ = ⟨b, hbP⟩ * ⟨a, haP⟩ :=
      hθ (by rw [map_mul, map_mul]; exact h)
    exact congrArg Subtype.val this
  · intro a ha
    obtain ⟨haP, ha'⟩ := mem_pull.1 ha
    have h := hsq _ ha'
    have : (⟨a, haP⟩ : ↥P) * ⟨a, haP⟩ = 1 := hθ (by rw [map_mul, map_one]; exact h)
    exact congrArg Subtype.val this

@[expose] def img (θ : ↥P →* Perm (Fin 7)) (D : Subgroup G) : Subgroup (Perm (Fin 7)) :=
  (D.subgroupOf P).map θ

theorem mem_img {θ : ↥P →* Perm (Fin 7)} {D : Subgroup G} {v : Perm (Fin 7)} :
    v ∈ img θ D ↔ ∃ (x : G) (hx : x ∈ P), x ∈ D ∧ θ ⟨x, hx⟩ = v := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.1, y.2, hy, rfl⟩
  · rintro ⟨x, hx, hxD, rfl⟩
    exact ⟨⟨x, hx⟩, hxD, rfl⟩

theorem img_le_range (θ : ↥P →* Perm (Fin 7)) (D : Subgroup G) : img θ D ≤ θ.range :=
  Subgroup.map_le_range _ _

theorem le_pull_img {θ : ↥P →* Perm (Fin 7)} {D : Subgroup G} (hD : D ≤ P) :
    D ≤ pull θ (img θ D) := by
  intro x hx
  exact mem_pull.2 ⟨hD hx, mem_img.2 ⟨x, hD hx, hx, rfl⟩⟩

theorem sq_img {θ : ↥P →* Perm (Fin 7)} {D : Subgroup G} (hEA : IsElementaryAbelian 2 ↥D) :
    ∀ v ∈ img θ D, v * v = 1 := by
  intro v hv
  obtain ⟨x, hx, hxD, rfl⟩ := mem_img.1 hv
  have h := sq_of_isElementaryAbelian hEA x hxD
  rw [← map_mul]
  have : (⟨x, hx⟩ : ↥P) * ⟨x, hx⟩ = 1 := Subtype.ext h
  rw [this, map_one]

theorem comm_img {θ : ↥P →* Perm (Fin 7)} {D : Subgroup G} (hEA : IsElementaryAbelian 2 ↥D) :
    ∀ v ∈ img θ D, ∀ w ∈ img θ D, v * w = w * v := by
  intro v hv w hw
  obtain ⟨x, hx, hxD, rfl⟩ := mem_img.1 hv
  obtain ⟨y, hy, hyD, rfl⟩ := mem_img.1 hw
  have h := comm_of_isElementaryAbelian hEA x hxD y hyD
  rw [← map_mul, ← map_mul]
  have : (⟨x, hx⟩ : ↥P) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ := Subtype.ext h
  rw [this]

theorem le_pull_V_or_W {θ : ↥P →* Perm (Fin 7)} (hrange : θ.range = modP0) {A : Subgroup G}
    (hAP : A ≤ P) (hA : IsElementaryAbelian 2 ↥A) :
    A ≤ pull θ IVK.A7.Vsub ∨ A ≤ pull θ IVK.A7.Wsub := by
  have hE : img θ A ≤ modP0 := hrange ▸ img_le_range θ A
  rcases le_V_or_le_W (img θ A) hE (sq_img hA) (comm_img hA) with h | h
  · exact Or.inl ((le_pull_img hAP).trans (pull_mono h))
  · exact Or.inr ((le_pull_img hAP).trans (pull_mono h))

theorem isFourSub_cases [Finite G] {θ : ↥P →* Perm (Fin 7)} (hθ : Function.Injective θ)
    (hrange : θ.range = modP0) {U : Subgroup G} (hU : IsFourSub P U) :
    U = pull θ IVK.A7.Vsub ∨ U = pull θ IVK.A7.Wsub := by
  obtain ⟨hUP, hEA, hcard⟩ := hU
  rcases le_pull_V_or_W hrange hUP hEA with h | h
  · left
    refine Subgroup.eq_of_le_of_card_ge h ?_
    rw [card_pull hθ (hrange ▸ Vsub_le_P0), card_Vsub, hcard]
  · right
    refine Subgroup.eq_of_le_of_card_ge h ?_
    rw [card_pull hθ (hrange ▸ Wsub_le_P0), card_Wsub, hcard]

end Transfer

section Model

variable {G : Type} [Group G] {K P : Subgroup G}

@[expose] noncomputable def rhoP (hPK : P ≤ K) (e : kBar K ≃* alternatingGroup (Fin 7)) :
    ↥P →* Perm (Fin 7) :=
  (alternatingGroup (Fin 7)).subtype.comp (e.toMonoidHom.comp
    ((QuotientGroup.mk' (pPrimeCore 2 ↥K)).comp (Subgroup.inclusion hPK)))

@[expose] noncomputable def thetaP (hPK : P ≤ K) (e : kBar K ≃* alternatingGroup (Fin 7))
    (g : Perm (Fin 7)) : ↥P →* Perm (Fin 7) :=
  (MulAut.conj g⁻¹).toMonoidHom.comp (rhoP hPK e)

theorem thetaP_apply (hPK : P ≤ K) (e : kBar K ≃* alternatingGroup (Fin 7)) (g : Perm (Fin 7))
    (x : ↥P) : thetaP hPK e g x = g⁻¹ * rhoP hPK e x * g := by
  simp [thetaP]

theorem thetaP_apply' (hPK : P ≤ K) (e : kBar K ≃* alternatingGroup (Fin 7)) (g : Perm (Fin 7))
    (x : G) (hx : x ∈ P) : thetaP hPK e g ⟨x, hx⟩ =
      g⁻¹ * ((e (QuotientGroup.mk (⟨x, hPK hx⟩ : ↥K)) : alternatingGroup (Fin 7)) : Perm (Fin 7)) *
        g :=
  thetaP_apply hPK e g ⟨x, hx⟩

theorem rhoP_injective [Finite G] (hP : IsSylowOf 2 P K) (e : kBar K ≃* alternatingGroup (Fin 7)) :
    Function.Injective (rhoP hP.le e) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h1 : e (QuotientGroup.mk (⟨x.1, hP.le x.2⟩ : ↥K)) = 1 := Subtype.ext hx
  have h2 : (QuotientGroup.mk (⟨x.1, hP.le x.2⟩ : ↥K) : kBar K) = 1 :=
    e.injective (h1.trans (map_one e).symm)
  have h3 : (⟨x.1, hP.le x.2⟩ : ↥K) ∈ pPrimeCore 2 ↥K := (QuotientGroup.eq_one_iff _).1 h2
  have h4 : x.1 ∈ pPrimeCoreOf 2 K :=
    C3.Layer1.Back.Setup91.mem_pPrimeCoreOf_iff.2 ⟨hP.le x.2, h3⟩
  have h5 : x.1 ∈ P ⊓ pPrimeCoreOf 2 K := ⟨x.2, h4⟩
  rw [C3.Layer1.Back.Setup91.inf_pPrimeCoreOf_eq_bot K hP.isPGroup, Subgroup.mem_bot] at h5
  exact Subtype.ext h5

theorem exists_conj [Finite G] (hP : IsSylowOf 2 P K) (e : kBar K ≃* alternatingGroup (Fin 7))
    (hcard : Nat.card ↥P = 8) :
    ∃ g : Perm (Fin 7), Function.Injective (thetaP hP.le e g) ∧
      (thetaP hP.le e g).range = modP0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hρ := rhoP_injective hP e
  have hrange_card : Nat.card ↥(rhoP hP.le e).range = 8 := by
    rw [← hcard]
    exact Nat.card_congr (MonoidHom.ofInjective hρ).toEquiv.symm
  have hrange_A : (rhoP hP.le e).range ≤ alternatingGroup (Fin 7) := by
    rintro _ ⟨x, rfl⟩
    exact (e _).2
  have hrange_p : IsPGroup 2 ↥(rhoP hP.le e).range :=
    IsPGroup.of_card (n := 3) (by rw [hrange_card]; norm_num)
  obtain ⟨T, hT⟩ := hrange_p.exists_le_sylow
  obtain ⟨g, hg⟩ := IVK.A7.exists_conj_T0 T
  have hTA : (T : Subgroup (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7) =
      modP0.map (MulAut.conj g).toMonoidHom := IVK.A7.T_inf_A7_eq_map hg
  have hTAcard : Nat.card ↥((T : Subgroup (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7)) = 8 := by
    rw [hTA, Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact IVK.A7.card_T0_inf_A7
  have hEq : (rhoP hP.le e).range = (T : Subgroup (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7) :=
    Subgroup.eq_of_le_of_card_ge (le_inf hT hrange_A) (by rw [hTAcard, hrange_card])
  refine ⟨g, (MulAut.conj g⁻¹).injective.comp hρ, ?_⟩
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    have hp : rhoP hP.le e p ∈ (T : Subgroup (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7) :=
      hEq ▸ ⟨p, rfl⟩
    rw [IVK.A7.mem_T_inf_A7 hg] at hp
    rw [mem_modP0_iff, thetaP_apply]
    exact hp
  · intro hx
    rw [mem_modP0_iff] at hx
    have h1 : g * x * g⁻¹ ∈ (T : Subgroup (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7) := by
      rw [IVK.A7.mem_T_inf_A7 hg]
      have : g⁻¹ * (g * x * g⁻¹) * g = x := by group
      rw [this]
      exact hx
    rw [← hEq] at h1
    obtain ⟨p, hp⟩ := h1
    refine ⟨p, ?_⟩
    rw [thetaP_apply, hp]
    group

@[expose] def movedLetters (K D : Subgroup G) (e : kBar K ≃* alternatingGroup (Fin 7)) :
    Set (Fin 7) :=
  {i | ∃ d ∈ D, ∃ hd : d ∈ K,
    ((e (QuotientGroup.mk (⟨d, hd⟩ : ↥K)) : alternatingGroup (Fin 7)) : Perm (Fin 7)) i ≠ i}

theorem movedLetters_pull (hPK : P ≤ K) (e : kBar K ≃* alternatingGroup (Fin 7))
    (g : Perm (Fin 7)) {V : Subgroup (Perm (Fin 7))} (hV : V ≤ (thetaP hPK e g).range) :
    movedLetters K (pull (thetaP hPK e g) V) e = (fun i => g i) '' moved V := by
  ext i
  constructor
  · rintro ⟨d, hd, hdK, hi⟩
    obtain ⟨hdP, hdV⟩ := mem_pull.1 hd
    refine ⟨g⁻¹ i, ⟨thetaP hPK e g ⟨d, hdP⟩, hdV, ?_⟩, by simp⟩
    rw [thetaP_apply', conj_ne_iff']
    simpa using hi
  · rintro ⟨j, ⟨v, hvV, hvj⟩, rfl⟩
    obtain ⟨x, rfl⟩ := hV hvV
    refine ⟨x.1, mem_pull.2 ⟨x.2, hvV⟩, hPK x.2, ?_⟩
    have h1 : (thetaP hPK e g ⟨x.1, x.2⟩) j ≠ j := hvj
    rw [thetaP_apply', conj_ne_iff'] at h1
    exact h1

theorem ncard_movedLetters_pull (hPK : P ≤ K) (e : kBar K ≃* alternatingGroup (Fin 7))
    (g : Perm (Fin 7)) {V : Subgroup (Perm (Fin 7))} (hV : V ≤ (thetaP hPK e g).range) :
    (movedLetters K (pull (thetaP hPK e g) V) e).ncard = (moved V).ncard := by
  rw [movedLetters_pull hPK e g hV]
  exact Set.ncard_image_of_injective _ g.injective

theorem ncard_movedLetters_eq (e₁ e₂ : kBar K ≃* alternatingGroup (Fin 7)) (D : Subgroup G) :
    (movedLetters K D e₂).ncard = (movedLetters K D e₁).ncard := by
  obtain ⟨τ, hτ⟩ : ∃ τ : Perm (Fin 7), ∀ k : kBar K,
      ((e₂ k : alternatingGroup (Fin 7)) : Perm (Fin 7)) =
        τ * ((e₁ k : alternatingGroup (Fin 7)) : Perm (Fin 7)) * τ⁻¹ := by
    refine ⟨C3.Layer1.Thm1.psiEquiv e₁ (e₂.trans e₁.symm), fun k => ?_⟩
    have h := C3.Layer1.Thm1.psi_apply e₁ (e₂.trans e₁.symm) k
    simpa using h
  have hset : movedLetters K D e₂ = (fun i => τ i) '' movedLetters K D e₁ := by
    ext i
    constructor
    · rintro ⟨d, hd, hdK, hi⟩
      refine ⟨τ⁻¹ i, ⟨d, hd, hdK, ?_⟩, by simp⟩
      rw [hτ, conj_ne_iff] at hi
      exact hi
    · rintro ⟨j, ⟨d, hd, hdK, hj⟩, rfl⟩
      refine ⟨d, hd, hdK, ?_⟩
      rw [hτ, conj_ne_iff]
      simpa using hj
  rw [hset]
  exact Set.ncard_image_of_injective _ τ.injective

end Model

theorem Vsub_le_range {G : Type} [Group G] {P : Subgroup G} {θ : ↥P →* Perm (Fin 7)}
    (hrange : θ.range = modP0) : IVK.A7.Vsub ≤ θ.range := by
  rw [hrange]; exact Vsub_le_P0

theorem Wsub_le_range {G : Type} [Group G] {P : Subgroup G} {θ : ↥P →* Perm (Fin 7)}
    (hrange : θ.range = modP0) : IVK.A7.Wsub ≤ θ.range := by
  rw [hrange]; exact Wsub_le_P0

theorem eq_pull_W {G : Type} [Group G] [Finite G] {K P D : Subgroup G} (hP : IsSylowOf 2 P K)
    (e : kBar K ≃* alternatingGroup (Fin 7)) (g : Perm (Fin 7))
    (hinj : Function.Injective (thetaP hP.le e g)) (hrange : (thetaP hP.le e g).range = modP0)
    (hD : D ≤ P) (hEA : IsElementaryAbelian 2 ↥D) (hcard : Nat.card ↥D = 4)
    (hcount : (movedLetters K D e).ncard = 6) : D = pull (thetaP hP.le e g) IVK.A7.Wsub := by
  rcases isFourSub_cases hinj hrange ⟨hD, hEA, hcard⟩ with h | h
  · exfalso
    rw [h, ncard_movedLetters_pull hP.le e g (Vsub_le_range hrange), moved_V] at hcount
    omega
  · exact h

end A7Aux

theorem card_sylow_A7 {G : Type} [Group G] [Finite G] {K P : Subgroup G}
    (hP : IsSylowOf 2 P K) (h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7))) :
    Nat.card ↥P = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := h7
  rw [hP.card_eq]
  have hK := Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥K)
  have hodd : Odd (Nat.card ↥(pPrimeCore 2 ↥K)) :=
    Nat.coprime_two_left.1 CFSG.pPrimeCore_coprime_card
  have h0 : Nat.card ↥(pPrimeCore 2 ↥K) ≠ 0 := Nat.card_pos.ne'
  have h1 : Nat.card (kBar K) ≠ 0 := Nat.card_pos.ne'
  have hA : Nat.card (kBar K) = 2520 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    decide
  have h2520 : (2520 : ℕ).factorization 2 = 3 := by
    have h : (2520 : ℕ) = 2 ^ 3 * 315 := by norm_num
    rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      C3.Layer1.Back.Setup91.factorization_two_of_odd (by decide : Odd 315)]
  rw [hK, Nat.factorization_mul h1 h0, Finsupp.add_apply,
    C3.Layer1.Back.Setup91.factorization_two_of_odd hodd, add_zero, hA, h2520]
  norm_num

theorem rankTwoShape_sylow_A7 {G : Type} [Group G] [Finite G] {K P : Subgroup G}
    (hP : IsSylowOf 2 P K) (h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7))) :
    RankTwoShape P := by
  obtain ⟨e⟩ := h7
  obtain ⟨g, hinj, hrange⟩ := A7Aux.exists_conj hP e (card_sylow_A7 hP ⟨e⟩)
  have hV := A7Aux.Vsub_le_range hrange
  have hW := A7Aux.Wsub_le_range hrange
  have hcV : Nat.card ↥(A7Aux.pull (A7Aux.thetaP hP.le e g) IVK.A7.Vsub) = 4 := by
    rw [A7Aux.card_pull hinj hV, A7Aux.card_Vsub]
  have hcW : Nat.card ↥(A7Aux.pull (A7Aux.thetaP hP.le e g) IVK.A7.Wsub) = 4 := by
    rw [A7Aux.card_pull hinj hW, A7Aux.card_Wsub]
  have hfourV : IsFourSub P (A7Aux.pull (A7Aux.thetaP hP.le e g) IVK.A7.Vsub) :=
    ⟨A7Aux.pull_le _ _, A7Aux.isElementaryAbelian_pull hinj A7Aux.comm_Vsub A7Aux.sq_Vsub, hcV⟩
  have hfourW : IsFourSub P (A7Aux.pull (A7Aux.thetaP hP.le e g) IVK.A7.Wsub) :=
    ⟨A7Aux.pull_le _ _, A7Aux.isElementaryAbelian_pull hinj A7Aux.comm_Wsub A7Aux.sq_Wsub, hcW⟩
  refine ⟨?_, ?_, ?_⟩
  · intro A hAP hA
    rcases A7Aux.le_pull_V_or_W hrange hAP hA with h | h
    · exact (Subgroup.card_le_of_le h).trans hcV.le
    · exact (Subgroup.card_le_of_le h).trans hcW.le
  · intro A hAP hA
    rcases A7Aux.le_pull_V_or_W hrange hAP hA with h | h
    · exact ⟨_, h, hfourV⟩
    · exact ⟨_, h, hfourW⟩
  · intro U₁ U₂ h₁ h₂
    obtain ⟨zp, hzp⟩ : IVK.A7.r ^ 2 ∈ (A7Aux.thetaP hP.le e g).range := by
      rw [hrange]; exact A7Aux.Vsub_le_P0 A7Aux.rsq_mem_V
    have hz : ∀ U : Subgroup G, IsFourSub P U → (zp : G) ∈ U := by
      intro U hU
      rcases A7Aux.isFourSub_cases hinj hrange hU with rfl | rfl
      · refine A7Aux.mem_pull.2 ⟨zp.2, ?_⟩
        show A7Aux.thetaP hP.le e g zp ∈ IVK.A7.Vsub
        rw [hzp]; exact A7Aux.rsq_mem_V
      · refine A7Aux.mem_pull.2 ⟨zp.2, ?_⟩
        show A7Aux.thetaP hP.le e g zp ∈ IVK.A7.Wsub
        rw [hzp]; exact A7Aux.rsq_mem_W
    refine ⟨(zp : G), hz U₁ h₁, hz U₂ h₂, ?_⟩
    rw [Subgroup.orderOf_coe, ← orderOf_injective _ hinj zp, hzp]
    exact A7Aux.orderOf_rsq

theorem exists_isDSub {G : Type} [Group G] [Finite G] {K P : Subgroup G}
    (hP : IsSylowOf 2 P K) (h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7))) :
    ∃ D, IsDSub K P D := by
  obtain ⟨e⟩ := h7
  obtain ⟨g, hinj, hrange⟩ := A7Aux.exists_conj hP e (card_sylow_A7 hP ⟨e⟩)
  refine ⟨A7Aux.pull (A7Aux.thetaP hP.le e g) IVK.A7.Wsub, A7Aux.pull_le _ _, hP.le,
    A7Aux.isElementaryAbelian_pull hinj A7Aux.comm_Wsub A7Aux.sq_Wsub, ?_, e, ?_⟩
  · rw [A7Aux.card_pull hinj (A7Aux.Wsub_le_range hrange), A7Aux.card_Wsub]
  · show (A7Aux.movedLetters K _ e).ncard = 6
    rw [A7Aux.ncard_movedLetters_pull hP.le e g (A7Aux.Wsub_le_range hrange)]
    exact A7Aux.moved_W

theorem isDSub_unique {G : Type} [Group G] [Finite G] {K P D₁ D₂ : Subgroup G}
    (hP : IsSylowOf 2 P K) (h₁ : IsDSub K P D₁) (h₂ : IsDSub K P D₂) : D₁ = D₂ := by
  obtain ⟨hD₁P, -, hEA₁, hcard₁, e₁, hcnt₁⟩ := h₁
  obtain ⟨hD₂P, -, hEA₂, hcard₂, e₂, hcnt₂⟩ := h₂
  obtain ⟨g, hinj, hrange⟩ := A7Aux.exists_conj hP e₁ (card_sylow_A7 hP ⟨e₁⟩)
  have hc₂ : (A7Aux.movedLetters K D₂ e₁).ncard = 6 := by
    rw [A7Aux.ncard_movedLetters_eq e₂ e₁ D₂]
    exact hcnt₂
  rw [A7Aux.eq_pull_W hP e₁ g hinj hrange hD₁P hEA₁ hcard₁ hcnt₁,
    A7Aux.eq_pull_W hP e₁ g hinj hrange hD₂P hEA₂ hcard₂ hc₂]

theorem isDSub_centralizer {G : Type} [Group G] [Finite G] {K P D : Subgroup G}
    (hP : IsSylowOf 2 P K) (hD : IsDSub K P D) :
    ∀ g ∈ P, (∀ d ∈ D, d * g = g * d) → g ∈ D := by
  obtain ⟨hDP, -, hEA, hcard, e, hcnt⟩ := hD
  obtain ⟨c, hinj, hrange⟩ := A7Aux.exists_conj hP e (card_sylow_A7 hP ⟨e⟩)
  have hDeq := A7Aux.eq_pull_W hP e c hinj hrange hDP hEA hcard hcnt
  intro g hg hcomm
  rw [hDeq] at hcomm ⊢
  refine A7Aux.mem_pull.2 ⟨hg, ?_⟩
  have hg0 : A7Aux.thetaP hP.le e c ⟨g, hg⟩ ∈ IVK.A7.P0list :=
    A7Aux.mem_modP0_iff.1 (hrange ▸ ⟨_, rfl⟩)
  refine A7Aux.centralizer_W _ hg0 ?_
  intro w hw
  obtain ⟨y, rfl⟩ := A7Aux.Wsub_le_range hrange hw
  have hy : (y : G) ∈ A7Aux.pull (A7Aux.thetaP hP.le e c) IVK.A7.Wsub :=
    A7Aux.mem_pull.2 ⟨y.2, hw⟩
  have h1 : (⟨g, hg⟩ : ↥P) * y = y * ⟨g, hg⟩ := Subtype.ext (hcomm y hy).symm
  rw [← map_mul, ← map_mul, h1]

end CFSG.GH74.GLS.Th2
