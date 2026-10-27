module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47abOPrime
public import CFSG.GH74.GLS.Stage4.T2Defs

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab

open CFSG.GH74.GLS CFSG.GH74.GLS.Stage4.Rest Subgroup
open scoped MatrixGroups

section Transport

theorem actsAsConj_map {Y G : Type} [Group Y] [Group G] (ι : Y →* G) (hι : Function.Injective ι)
    {I : Subgroup Y} {F : Type} [Field F] {t : Y} {e : ↥I ≃* SL(2, F)} {g : GL (Fin 2) F}
    (h : ConjData t I e g) :
    ActsAsConj (ι t) (I.map ι) ((Subgroup.equivMapOfInjective I ι hι).symm.trans e) g := by
  intro x
  obtain ⟨a, ha, hax⟩ := x.2
  obtain ⟨y', hy', hmat⟩ := h ⟨a, ha⟩
  have hx : Subgroup.equivMapOfInjective I ι hι ⟨a, ha⟩ = x := Subtype.ext hax
  refine ⟨Subgroup.equivMapOfInjective I ι hι y', ?_, ?_⟩
  · show ι (y' : Y) = ι t * (x : G) * (ι t)⁻¹
    rw [hy', ← hax, map_mul, map_mul, map_inv]
  · show ((e ((Subgroup.equivMapOfInjective I ι hι).symm
        (Subgroup.equivMapOfInjective I ι hι y')) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = _
    rw [MulEquiv.symm_apply_apply]
    have : (Subgroup.equivMapOfInjective I ι hι).symm x = ⟨a, ha⟩ := by
      rw [← hx, MulEquiv.symm_apply_apply]
    show _ = (g : Matrix (Fin 2) (Fin 2) F) *
      ((e ((Subgroup.equivMapOfInjective I ι hι).symm x) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *
        ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
    rw [this]
    exact hmat

theorem map_centralizer_singleton {G G' : Type*} [Group G] [Group G'] (φ : G ≃* G') (z : G) :
    (centralizer ({z} : Set G)).map φ.toMonoidHom = centralizer ({φ z} : Set G') := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul, hx]
  · intro hy
    refine ⟨φ.symm y, ?_, by simp⟩
    apply φ.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact hy

theorem Ch6Rem.map {G G' : Type} [Group G] [Group G'] (φ : G ≃* G') {z : G} {K₁ K₂ : Subgroup G}
    {F₁ F₂ : Type} [Field F₁] [Field F₂] {t : G} (h : Ch6Rem z K₁ K₂ F₁ F₂ t) :
    Ch6Rem (φ z) (K₁.map φ.toMonoidHom) (K₂.map φ.toMonoidHom) F₁ F₂ (φ t) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, ← map_mul, h.comm_z]
  · rw [← map_mul, h.sq, map_one]
  · rw [← map_centralizer_singleton, ← map_oPrimeResidualOf, ← h.gen, Subgroup.map_sup,
      Subgroup.map_sup, MonoidHom.map_zpowers]
    rfl
  · obtain ⟨e, g, hns, hact⟩ := h.diag₁
    exact ⟨(Subgroup.equivMapOfInjective K₁ φ.toMonoidHom φ.injective).symm.trans e, g, hns,
      actsAsConj_map φ.toMonoidHom φ.injective hact⟩
  · obtain ⟨e, g, hns, hact⟩ := h.diag₂
    exact ⟨(Subgroup.equivMapOfInjective K₂ φ.toMonoidHom φ.injective).symm.trans e, g, hns,
      actsAsConj_map φ.toMonoidHom φ.injective hact⟩

theorem ch6Data_map {G G' : Type} [Group G] [Group G'] (φ : G ≃* G') {z : G} {K₁ K₂ : Subgroup G}
    {F₁ F₂ : Type} [Field F₁] [Field F₂] {t : G}
    (h : (∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) ∧ z ∈ K₁ ∧ z ∈ K₂ ∧ K₁ ⊓ K₂ = zpowers z ∧
      Ch6Rem z K₁ K₂ F₁ F₂ t) :
    (∀ x ∈ K₁.map φ.toMonoidHom, ∀ y ∈ K₂.map φ.toMonoidHom, x * y = y * x) ∧
      φ z ∈ K₁.map φ.toMonoidHom ∧ φ z ∈ K₂.map φ.toMonoidHom ∧
      K₁.map φ.toMonoidHom ⊓ K₂.map φ.toMonoidHom = zpowers (φ z) ∧
      Ch6Rem (φ z) (K₁.map φ.toMonoidHom) (K₂.map φ.toMonoidHom) F₁ F₂ (φ t) := by
  obtain ⟨hc, hz₁, hz₂, hi, hR⟩ := h
  refine ⟨?_, ⟨z, hz₁, rfl⟩, ⟨z, hz₂, rfl⟩, ?_, Ch6Rem.map φ hR⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    show φ a * φ b = φ b * φ a
    rw [← map_mul, ← map_mul, hc a ha b hb]
  · rw [← Subgroup.map_inf_eq _ _ _ φ.injective, hi, MonoidHom.map_zpowers]
    rfl

end Transport

section FromShape

variable {M : Type} [Group M] {F₁ F₂ : Type} [Field F₁] [Field F₂]

theorem Shape.oPrimeResidualOf_eq [Finite F₁] [Finite F₂] {C : Subgroup M} (S : Shape ↥C F₁ F₂)
    (h₁ : 4 ≤ Nat.card F₁) (h₂ : 4 ≤ Nat.card F₂) : oPrimeResidualOf 2 C = C := by
  rw [oPrimeResidualOf, S.oPrimeResidual_eq_top h₁ h₂, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

theorem Shape.exists_ch6Rem_aux [Finite F₁] [Finite F₂] {C : Subgroup M} {z : M}
    (hC : C = centralizer ({z} : Set M)) (S : Shape ↥C F₁ F₂) (hz : (S.z : M) = z)
    (h₁ : 4 ≤ Nat.card F₁) (h₂ : 4 ≤ Nat.card F₂) :
    ∃ (K₁ K₂ : Subgroup M) (t : M), (∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) ∧ z ∈ K₁ ∧ z ∈ K₂ ∧
      K₁ ⊓ K₂ = zpowers z ∧ Ch6Rem z K₁ K₂ F₁ F₂ t := by
  have hinj : Function.Injective C.subtype := Subtype.val_injective
  have hO : oPrimeResidualOf 2 (centralizer ({z} : Set M)) = C := by
    rw [← hC]
    exact S.oPrimeResidualOf_eq h₁ h₂
  have hgenC : S.I₁.map C.subtype ⊔ S.I₂.map C.subtype ⊔ zpowers (S.t : M) = C := by
    have h := congrArg (Subgroup.map C.subtype) S.gen
    rw [Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h
    exact h
  have key : ∀ x : M, x ∈ C → x * z = z * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.1 (hC ▸ hx)
  have hzC : (S.t : M) * z = z * (S.t : M) := key _ S.t.2
  refine ⟨S.I₁.map C.subtype, S.I₂.map C.subtype, (S.t : M), ?_, ⟨S.z, S.z_mem₁, hz⟩,
    ⟨S.z, S.z_mem₂, hz⟩, ?_, hzC, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (S.comm a ha b hb)
  · rw [← Subgroup.map_inf_eq _ _ _ hinj, S.inter, MonoidHom.map_zpowers, Subgroup.coe_subtype, hz]
  · exact congrArg Subtype.val S.t_sq
  · rw [hgenC, hO]
  · exact ⟨(Subgroup.equivMapOfInjective S.I₁ C.subtype hinj).symm.trans S.e₁, S.g₁, S.ns₁,
      actsAsConj_map C.subtype hinj S.act₁⟩
  · exact ⟨(Subgroup.equivMapOfInjective S.I₂ C.subtype hinj).symm.trans S.e₂, S.g₂, S.ns₂,
      actsAsConj_map C.subtype hinj S.act₂⟩

theorem Shape.exists_ch6Rem [Finite F₁] [Finite F₂] {z : M}
    (S : Shape ↥(centralizer ({z} : Set M)) F₁ F₂) (hz : (S.z : M) = z)
    (h₁ : 4 ≤ Nat.card F₁) (h₂ : 4 ≤ Nat.card F₂) :
    ∃ (K₁ K₂ : Subgroup M) (t : M), (∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) ∧ z ∈ K₁ ∧ z ∈ K₂ ∧
      K₁ ⊓ K₂ = zpowers z ∧ Ch6Rem z K₁ K₂ F₁ F₂ t :=
  Shape.exists_ch6Rem_aux rfl S hz h₁ h₂

end FromShape

section ToShape

theorem subgroupOf_zpowers {G : Type*} [Group G] (L : Subgroup G) {t : G} (ht : t ∈ L) :
    (zpowers t).subgroupOf L = zpowers (⟨t, ht⟩ : ↥L) := by
  ext y
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, Subtype.ext (by rw [Subgroup.coe_zpow]; exact hn)⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [← hn]; rfl⟩

theorem conjData_subgroupOf {G : Type} [Group G] {L K : Subgroup G} (hKL : K ≤ L) {t : G}
    (ht : t ∈ L) {F : Type} [Field F] {e : ↥K ≃* SL(2, F)} {g : GL (Fin 2) F}
    (h : ActsAsConj t K e g) :
    ConjData (⟨t, ht⟩ : ↥L) (K.subgroupOf L) ((Subgroup.subgroupOfEquivOfLe hKL).trans e) g := by
  intro x
  obtain ⟨y, hy, hmat⟩ := h ⟨x.1.1, x.2⟩
  exact ⟨⟨⟨y.1, hKL y.2⟩, y.2⟩, Subtype.ext hy, hmat⟩

theorem exists_shape_of_diag_aux {H : Type} [Group H] {z : H} {K₁ K₂ L : Subgroup H}
    {F₁ F₂ : Type} [Field F₁] [Field F₂] {t : H} (hL : K₁ ⊔ K₂ ⊔ zpowers t = L)
    (hsq : t * t = 1)
    (hd₁ : ∃ (e : ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F₁) (g : GL (Fin 2) F₁),
      ¬ IsSquare ((Matrix.GeneralLinearGroup.det g : F₁ˣ) : F₁) ∧ ActsAsConj t K₁ e g)
    (hd₂ : ∃ (e : ↥K₂ ≃* Matrix.SpecialLinearGroup (Fin 2) F₂) (g : GL (Fin 2) F₂),
      ¬ IsSquare ((Matrix.GeneralLinearGroup.det g : F₂ˣ) : F₂) ∧ ActsAsConj t K₂ e g)
    (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x)
    (hinter : K₁ ⊓ K₂ = zpowers z) (hz : orderOf z = 2) :
    Nonempty (Shape ↥L F₁ F₂) := by
  obtain ⟨e₁, g₁, hn₁, ha₁⟩ := hd₁
  obtain ⟨e₂, g₂, hn₂, ha₂⟩ := hd₂
  have hz₁ : z ∈ K₁ := (show z ∈ K₁ ⊓ K₂ by rw [hinter]; exact Subgroup.mem_zpowers z).1
  have hK₁L : K₁ ≤ L := hL ▸ le_trans le_sup_left le_sup_left
  have hK₂L : K₂ ≤ L := hL ▸ le_trans le_sup_right le_sup_left
  have htL : t ∈ L := hL ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hzL : z ∈ L := hK₁L hz₁
  have hzz : z * z = 1 := by rw [← pow_two, ← hz]; exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz
    exact absurd hz (by norm_num)
  have hgen : K₁.subgroupOf L ⊔ K₂.subgroupOf L ⊔ zpowers (⟨t, htL⟩ : ↥L) = ⊤ := by
    rw [← subgroupOf_zpowers L htL, ← Subgroup.subgroupOf_sup hK₁L hK₂L,
      ← Subgroup.subgroupOf_sup (sup_le hK₁L hK₂L) ((Subgroup.zpowers_le).2 htL), hL,
      Subgroup.subgroupOf_self]
  exact ⟨{
    I₁ := K₁.subgroupOf L
    I₂ := K₂.subgroupOf L
    z := ⟨z, hzL⟩
    t := ⟨t, htL⟩
    e₁ := (Subgroup.subgroupOfEquivOfLe hK₁L).trans e₁
    e₂ := (Subgroup.subgroupOfEquivOfLe hK₂L).trans e₂
    g₁ := g₁
    g₂ := g₂
    comm := fun a ha b hb => Subtype.ext (hcomm a.1 ha b.1 hb)
    inter := by
      have h : (K₁ ⊓ K₂).subgroupOf L = K₁.subgroupOf L ⊓ K₂.subgroupOf L :=
        Subgroup.comap_inf _ _ _
      rw [← h, hinter, subgroupOf_zpowers L hzL]
    z_sq := Subtype.ext hzz
    z_ne := fun h => hz1 (congrArg Subtype.val h)
    gen := hgen
    t_sq := Subtype.ext hsq
    ns₁ := hn₁
    ns₂ := hn₂
    act₁ := conjData_subgroupOf hK₁L htL ha₁
    act₂ := conjData_subgroupOf hK₂L htL ha₂ }⟩

theorem exists_shape_of_diag {H : Type} [Group H] {z : H} {K₁ K₂ : Subgroup H} {F₁ F₂ : Type}
    [Field F₁] [Field F₂] {t : H} (hsq : t * t = 1)
    (hd₁ : ∃ (e : ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F₁) (g : GL (Fin 2) F₁),
      ¬ IsSquare ((Matrix.GeneralLinearGroup.det g : F₁ˣ) : F₁) ∧ ActsAsConj t K₁ e g)
    (hd₂ : ∃ (e : ↥K₂ ≃* Matrix.SpecialLinearGroup (Fin 2) F₂) (g : GL (Fin 2) F₂),
      ¬ IsSquare ((Matrix.GeneralLinearGroup.det g : F₂ˣ) : F₂) ∧ ActsAsConj t K₂ e g)
    (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x)
    (hinter : K₁ ⊓ K₂ = zpowers z) (hz : orderOf z = 2) :
    Nonempty (Shape ↥(K₁ ⊔ K₂ ⊔ zpowers t) F₁ F₂) :=
  exists_shape_of_diag_aux rfl hsq hd₁ hd₂ hcomm hinter hz

theorem Ch6Rem.exists_shape {H : Type} [Group H] {z : H} {K₁ K₂ : Subgroup H} {F₁ F₂ : Type}
    [Field F₁] [Field F₂] {t : H} (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t)
    (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x)
    (hinter : K₁ ⊓ K₂ = zpowers z) (hz : orderOf z = 2) :
    Nonempty (Shape ↥(K₁ ⊔ K₂ ⊔ zpowers t) F₁ F₂) :=
  exists_shape_of_diag hRem.sq hRem.diag₁ hRem.diag₂ hcomm hinter hz

end ToShape

end CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab
