module

public import CFSG.CGT.PushingUpLit.BHS5.FiveSixQuot

public section

namespace CFSG.CGT.PushingUpLit.BHS5

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne CFSG.Open CFSG.LieType.BorelTits
  CFSG.CGT.PushingUpLit.BHS

variable {V : Type} [CommGroup V]

@[expose] noncomputable def liftQ (P : Subgroup (MulAut V)) (E' : Subgroup (MulAut (V ⧸ fixOp P))) :
    Subgroup (MulAut V) :=
  (E'.comap (quotHom P)).map P.subtype

section Lift

variable {P : Subgroup (MulAut V)}

theorem mem_liftQ {E' : Subgroup (MulAut (V ⧸ fixOp P))} {x : MulAut V} :
    x ∈ liftQ P E' ↔ ∃ hx : x ∈ P, quotHom P ⟨x, hx⟩ ∈ E' := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem liftQ_le (E' : Subgroup (MulAut (V ⧸ fixOp P))) : liftQ P E' ≤ P :=
  Subgroup.map_subtype_le _

theorem liftQ_mono {E₁' E₂' : Subgroup (MulAut (V ⧸ fixOp P))} (h : E₁' ≤ E₂') :
    liftQ P E₁' ≤ liftQ P E₂' :=
  Subgroup.map_mono (Subgroup.comap_mono h)

theorem liftQ_quotImg (hinj : Function.Injective (quotHom P)) {E : Subgroup (MulAut V)}
    (hEP : E ≤ P) : liftQ P ((E.subgroupOf P).map (quotHom P)) = E := by
  ext x
  rw [mem_liftQ]
  constructor
  · rintro ⟨hx, y, hy, hyx⟩
    have hyx' : y = ⟨x, hx⟩ := hinj hyx
    rw [hyx'] at hy
    exact Subgroup.mem_subgroupOf.1 hy
  · intro hx
    exact ⟨hEP hx, ⟨x, hEP hx⟩, hx, rfl⟩

theorem quotImg_liftQ {E' : Subgroup (MulAut (V ⧸ fixOp P))}
    (hE' : E' ≤ (⊤ : Subgroup ↥P).map (quotHom P)) :
    ((liftQ P E').subgroupOf P).map (quotHom P) = E' := by
  ext q
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨_, h⟩ := mem_liftQ.1 (Subgroup.mem_subgroupOf.1 hy)
    exact h
  · intro hq
    obtain ⟨y, -, rfl⟩ := hE' hq
    exact ⟨y, Subgroup.mem_subgroupOf.2 (mem_liftQ.2 ⟨y.2, hq⟩), rfl⟩

theorem mem_fixV_of_mk_mem (hV : ∀ v : V, v ^ 2 = 1) {Y : Subgroup (MulAut V)} (hYP : Y ≤ P)
    (hYgen : Y ≤ Subgroup.closure {x | x ∈ Y ∧ Odd (orderOf x)}) {v : V}
    (hv : (QuotientGroup.mk v : V ⧸ fixOp P) ∈ fixV ((Y.subgroupOf P).map (quotHom P))) :
    v ∈ fixV Y := by
  have hYO : Y ≤ opResidual 2 P := by
    refine hYgen.trans ((Subgroup.closure_le _).2 fun x hx => ?_)
    exact mem_opResidual_of_coprime (hYP hx.1) (Nat.coprime_two_right.2 hx.2)
  have hq : ∀ k ∈ Y, ∀ k' ∈ Y, k' (k v * v⁻¹) = k v * v⁻¹ := by
    intro k hk k' hk'
    have h1 : k v * v⁻¹ ∈ fixOp P := by
      have h2 := hv (quotHom P ⟨k, hYP hk⟩) ⟨⟨k, hYP hk⟩, hk, rfl⟩
      rw [quotHom_mk] at h2
      simpa [div_eq_mul_inv] using QuotientGroup.eq_iff_div_mem.1 h2
    exact h1 k' (hYO hk')
  exact fix_of_quad_oddGen hV hYgen hq

theorem commV_quotImg {E : Subgroup (MulAut V)} (hEP : E ≤ P) :
    (commV E).map (QuotientGroup.mk' (fixOp P)) = commV ((E.subgroupOf P).map (quotHom P)) := by
  rw [commV, commV, MonoidHom.map_closure]
  congr 1
  ext w
  constructor
  · rintro ⟨_, ⟨x, hx, v, rfl⟩, rfl⟩
    refine ⟨quotHom P ⟨x, hEP hx⟩, ⟨⟨x, hEP hx⟩, hx, rfl⟩, QuotientGroup.mk v, ?_⟩
    rw [quotHom_mk]
    rfl
  · rintro ⟨_, ⟨y, hy, rfl⟩, u, rfl⟩
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective u
    refine ⟨y.1 v * v⁻¹, ⟨y.1, hy, v, rfl⟩, ?_⟩
    rw [quotHom_mk]
    rfl

theorem commV_le_fixV_of_quot (hV : ∀ v : V, v ^ 2 = 1) {X Y : Subgroup (MulAut V)}
    (hXP : X ≤ P) (hYP : Y ≤ P) (hYgen : Y ≤ Subgroup.closure {x | x ∈ Y ∧ Odd (orderOf x)})
    (h : commV ((X.subgroupOf P).map (quotHom P)) ≤ fixV ((Y.subgroupOf P).map (quotHom P))) :
    commV X ≤ fixV Y := by
  intro w hw
  refine mem_fixV_of_mk_mem hV hYP hYgen (h ?_)
  rw [← commV_quotImg hXP]
  exact Subgroup.mem_map_of_mem (QuotientGroup.mk' (fixOp P)) hw

theorem conjSub_liftQ {t : MulAut V} (ht : t ∈ P) {E' : Subgroup (MulAut (V ⧸ fixOp P))} :
    conjSub t (liftQ P E') = liftQ P (conjSub (quotHom P ⟨t, ht⟩) E') := by
  ext x
  rw [mem_conjSub_iff, mem_liftQ, mem_liftQ]
  have key : ∀ (hx : x ∈ P) (hx' : t⁻¹ * x * t ∈ P), quotHom P ⟨t⁻¹ * x * t, hx'⟩ =
      (quotHom P ⟨t, ht⟩)⁻¹ * quotHom P ⟨x, hx⟩ * quotHom P ⟨t, ht⟩ := by
    intro hx hx'
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  constructor
  · rintro ⟨hx', h⟩
    have hx : x ∈ P := by
      have := P.mul_mem (P.mul_mem ht hx') (P.inv_mem ht)
      simpa [mul_assoc] using this
    refine ⟨hx, ?_⟩
    rw [mem_conjSub_iff, ← key hx hx']
    exact h
  · rintro ⟨hx, h⟩
    rw [mem_conjSub_iff] at h
    have hx' : t⁻¹ * x * t ∈ P := P.mul_mem (P.mul_mem (P.inv_mem ht) hx) ht
    exact ⟨hx', by rw [key hx hx']; exact h⟩

theorem le_normalizer_liftQ_iff {E' Y' : Subgroup (MulAut (V ⧸ fixOp P))}
    (hE' : E' ≤ (⊤ : Subgroup ↥P).map (quotHom P))
    (hY' : Y' ≤ (⊤ : Subgroup ↥P).map (quotHom P)) :
    liftQ P Y' ≤ Subgroup.normalizer (liftQ P E' : Set (MulAut V)) ↔
      Y' ≤ Subgroup.normalizer (E' : Set (MulAut (V ⧸ fixOp P))) := by
  have hrange : E' ≤ (quotHom P).range := by
    rw [MonoidHom.range_eq_map]
    exact hE'
  have h1 : (liftQ P E').subgroupOf P = E'.comap (quotHom P) :=
    Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
  have key : (Subgroup.normalizer (liftQ P E' : Set (MulAut V))).subgroupOf P =
      (Subgroup.normalizer (E' : Set (MulAut (V ⧸ fixOp P)))).comap (quotHom P) := by
    rw [Subgroup.subgroupOf_normalizer_eq (liftQ_le E'), h1,
      Subgroup.comap_normalizer_eq_of_le_range hrange]
  constructor
  · intro h y' hy'
    obtain ⟨y, -, rfl⟩ := hY' hy'
    have h2 : (y : MulAut V) ∈ Subgroup.normalizer (liftQ P E' : Set (MulAut V)) :=
      h (mem_liftQ.2 ⟨y.2, hy'⟩)
    have h3 : y ∈ (Subgroup.normalizer (liftQ P E' : Set (MulAut V))).subgroupOf P := h2
    rw [key] at h3
    exact h3
  · intro h y hy
    obtain ⟨hyP, hyY⟩ := mem_liftQ.1 hy
    have h3 : (⟨y, hyP⟩ : ↥P) ∈
        (Subgroup.normalizer (liftQ P E' : Set (MulAut V))).subgroupOf P := by
      rw [key]
      exact h hyY
    exact h3

@[expose] noncomputable def quotImgEquiv (hinj : Function.Injective (quotHom P))
    {E : Subgroup (MulAut V)} (hEP : E ≤ P) :
    ↥E ≃* ↥((E.subgroupOf P).map (quotHom P)) :=
  (Subgroup.subgroupOfEquivOfLe hEP).symm.trans (Subgroup.equivMapOfInjective _ (quotHom P) hinj)

@[expose] noncomputable def commVQuot {E : Subgroup (MulAut V)} (hEP : E ≤ P) :
    ↥(commV E) →* ↥(commV ((E.subgroupOf P).map (quotHom P))) :=
  MonoidHom.codRestrict ((QuotientGroup.mk' (fixOp P)).comp (commV E).subtype) _ fun w => by
    rw [← commV_quotImg hEP]
    exact Subgroup.mem_map_of_mem _ w.2

theorem commVQuot_surjective {E : Subgroup (MulAut V)} (hEP : E ≤ P) :
    Function.Surjective (commVQuot hEP) := by
  intro u
  have hu : (u : V ⧸ fixOp P) ∈ (commV E).map (QuotientGroup.mk' (fixOp P)) := by
    rw [commV_quotImg hEP]
    exact u.2
  obtain ⟨w, hw, hwu⟩ := hu
  exact ⟨⟨w, hw⟩, Subtype.ext hwu⟩

theorem commVQuot_mem_iff (hV : ∀ v : V, v ^ 2 = 1) {E : Subgroup (MulAut V)} (hEP : E ≤ P)
    (hEgen : E ≤ Subgroup.closure {x | x ∈ E ∧ Odd (orderOf x)}) (w : ↥(commV E)) :
    commVQuot hEP w ∈ (commV ((E.subgroupOf P).map (quotHom P)) ⊓
      fixV ((E.subgroupOf P).map (quotHom P))).subgroupOf
        (commV ((E.subgroupOf P).map (quotHom P))) ↔
      w ∈ (commV E ⊓ fixV E).subgroupOf (commV E) := by
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_inf]
  constructor
  · rintro ⟨-, h⟩
    exact ⟨w.2, mem_fixV_of_mk_mem hV hEP hEgen h⟩
  · rintro ⟨-, h⟩
    exact ⟨(commVQuot hEP w).2, mk_mem_fixV_map h⟩

end Lift

theorem map_mem_commV_of_mem {E : Subgroup (MulAut V)} {x : MulAut V} (hx : x ∈ E) {p : V}
    (hp : p ∈ commV E) : x p ∈ commV E :=
  CFSG.Quasithin.commV_apply_mem_of_mem hx hp

theorem natSection_transfer {V' H K : Type*} [CommGroup V'] [Group K] [Mul H] (act : H → K → K)
    {X : Subgroup (MulAut V)} {W Z : Subgroup V} {X' : Subgroup (MulAut V')} {W' Z' : Subgroup V'}
    (ι : ↥X ≃* ↥X') (π : ↥W →* ↥W') (hπ : Function.Surjective π)
    (hker : ∀ p : ↥W, π p ∈ Z'.subgroupOf W' ↔ p ∈ Z.subgroupOf W)
    (hequiv : ∀ (x : ↥X) (p : ↥W) (hp : (x : MulAut V) p ∈ W),
      ((π ⟨(x : MulAut V) p, hp⟩ : ↥W') : V') = ((ι x : ↥X') : MulAut V') ((π p : ↥W') : V'))
    (h : ∃ (θ : ↥X' ≃* H) (β : ↥W' →* K), Function.Surjective β ∧ β.ker = Z'.subgroupOf W' ∧
      ∀ (x : ↥X') (p : ↥W') (hp : (x : MulAut V') p ∈ W'),
        β ⟨(x : MulAut V') p, hp⟩ = act (θ x) (β p)) :
    ∃ (θ : ↥X ≃* H) (β : ↥W →* K), Function.Surjective β ∧ β.ker = Z.subgroupOf W ∧
      ∀ (x : ↥X) (p : ↥W) (hp : (x : MulAut V) p ∈ W),
        β ⟨(x : MulAut V) p, hp⟩ = act (θ x) (β p) := by
  obtain ⟨θ, β, hsurj, hkerβ, hβ⟩ := h
  refine ⟨ι.trans θ, β.comp π, hsurj.comp hπ, ?_, ?_⟩
  · ext p
    have h1 : p ∈ (β.comp π).ker ↔ π p ∈ β.ker := Iff.rfl
    rw [h1, hkerβ, hker]
  · intro x p hp
    have hp' : ((ι x : ↥X') : MulAut V') ((π p : ↥W') : V') ∈ W' := by
      rw [← hequiv x p hp]
      exact (π ⟨_, hp⟩).2
    have h1 : π ⟨(x : MulAut V) p, hp⟩ =
        ⟨((ι x : ↥X') : MulAut V') ((π p : ↥W') : V'), hp'⟩ :=
      Subtype.ext (hequiv x p hp)
    show β (π ⟨(x : MulAut V) p, hp⟩) = act (θ (ι x)) (β (π p))
    rw [h1]
    exact hβ (ι x) (π p) hp'

section Natural

variable {P : Subgroup (MulAut V)}

theorem isSLNatSection_of_quot (hV : ∀ v : V, v ^ 2 = 1) (hinj : Function.Injective (quotHom P))
    {n : ℕ} {E : Subgroup (MulAut V)} (hEP : E ≤ P)
    (hEgen : E ≤ Subgroup.closure {x | x ∈ E ∧ Odd (orderOf x)})
    (h : IsSLNatSection ((E.subgroupOf P).map (quotHom P))
      (commV ((E.subgroupOf P).map (quotHom P)))
      (commV ((E.subgroupOf P).map (quotHom P)) ⊓ fixV ((E.subgroupOf P).map (quotHom P))) n) :
    IsSLNatSection E (commV E) (commV E ⊓ fixV E) n :=
  ⟨fun _ hx _ hp => map_mem_commV_of_mem hx hp,
    natSection_transfer (fun (g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
      (v : Multiplicative (Fin 2 → GaloisField 2 n)) => Multiplicative.ofAdd
        ((g : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec (Multiplicative.toAdd v)))
      (quotImgEquiv hinj hEP) (commVQuot hEP) (commVQuot_surjective hEP)
      (commVQuot_mem_iff hV hEP hEgen) (fun _ _ _ => rfl) h.2⟩

theorem isAltNatSection_of_quot (hV : ∀ v : V, v ^ 2 = 1) (hinj : Function.Injective (quotHom P))
    {m : ℕ} {E : Subgroup (MulAut V)} (hEP : E ≤ P)
    (hEgen : E ≤ Subgroup.closure {x | x ∈ E ∧ Odd (orderOf x)})
    (h : IsAltNatSection ((E.subgroupOf P).map (quotHom P))
      (commV ((E.subgroupOf P).map (quotHom P)))
      (commV ((E.subgroupOf P).map (quotHom P)) ⊓ fixV ((E.subgroupOf P).map (quotHom P))) m) :
    IsAltNatSection E (commV E) (commV E ⊓ fixV E) m :=
  ⟨fun _ hx _ hp => map_mem_commV_of_mem hx hp,
    natSection_transfer (fun (σ : alternatingGroup (Fin m)) (v : ↥(G6.coreMod m)) =>
        G6.coreAct m (σ : Equiv.Perm (Fin m)) v)
      (quotImgEquiv hinj hEP) (commVQuot hEP) (commVQuot_surjective hEP)
      (commVQuot_mem_iff hV hEP hEgen) (fun _ _ _ => rfl) h.2⟩

end Natural

end CFSG.CGT.PushingUpLit.BHS5
