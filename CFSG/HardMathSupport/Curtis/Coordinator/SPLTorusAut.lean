module

public import CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977StandardCyclic
public import CFSG.HardMathSupport.Curtis.Proving.ToralQuotient
public import CFSG.LocalAnalysis.AGLEmbedding.SPLMSide

public section

open CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

namespace CFSG.HardMathSupport.Curtis.Coordinator

@[expose] def autFix {S : Type*} [Group S] (ζ : MulAut S) : Subgroup S where
  carrier := {s | ζ s = s}
  mul_mem' := by
    intro a b ha hb
    show ζ (a * b) = a * b
    rw [map_mul, show ζ a = a from ha, show ζ b = b from hb]
  one_mem' := map_one _
  inv_mem' := by
    intro a ha
    show ζ a⁻¹ = a⁻¹
    rw [map_inv, show ζ a = a from ha]

theorem mem_autFix {S : Type*} [Group S] (ζ : MulAut S) (s : S) : s ∈ autFix ζ ↔ ζ s = s :=
  Iff.rfl

variable {Y : Type*} [Group Y]

theorem isSolvable_autFix {L : Subgroup Y} [Group.IsPerfect L] {u : Y}
    (hu : u ∈ Subgroup.normalizer (L : Set Y))
    (hsolv : Group.IsSolvable ↥(L ⊓ Subgroup.centralizer ({u} : Set Y))) :
    Group.IsSolvable ↥(autFix (automizer L ⟨u, hu⟩)) := by
  set ζ := automizer L ⟨u, hu⟩ with hζ
  set cu : MulAut L := L.normalizerMonoidHom ⟨u, hu⟩ with hcu
  have hcu_apply : ∀ l : L, ((cu l : L) : Y) = u * l * u⁻¹ := fun l => rfl
  have hzeta : ∀ l : L, ζ (QuotientGroup.mk l) = QuotientGroup.mk (cu l) := fun l =>
    automizer_apply_mk L ⟨u, hu⟩ l
  let M : Subgroup L := (autFix ζ).comap (QuotientGroup.mk' (Subgroup.center L))
  have hMmem : ∀ l : L, l ∈ M ↔ (cu l)⁻¹ * l ∈ Subgroup.center L := by
    intro l
    show ζ (QuotientGroup.mk l) = QuotientGroup.mk l ↔ _
    rw [hzeta, QuotientGroup.eq]
  let κ : M →* Subgroup.center L :=
    { toFun := fun l => ⟨(cu l.1)⁻¹ * l.1, (hMmem l.1).1 l.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro a b
        apply Subtype.ext
        have hz := (hMmem a.1).1 a.2
        have hc := Subgroup.mem_center_iff.mp hz
        change (cu (a.1 * b.1))⁻¹ * (a.1 * b.1) = ((cu a.1)⁻¹ * a.1) * ((cu b.1)⁻¹ * b.1)
        rw [map_mul]
        calc (cu a.1 * cu b.1)⁻¹ * (a.1 * b.1)
            = (cu b.1)⁻¹ * ((cu a.1)⁻¹ * a.1) * b.1 := by group
          _ = ((cu a.1)⁻¹ * a.1) * ((cu b.1)⁻¹ * b.1) := by
            rw [hc ((cu b.1)⁻¹)]; group }
  have hker : ∀ k : κ.ker, ((k.1.1 : L) : Y) ∈ L ⊓ Subgroup.centralizer ({u} : Set Y) := by
    intro k
    refine ⟨k.1.1.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h := k.2
    rw [MonoidHom.mem_ker] at h
    have h1 : (cu k.1.1)⁻¹ * k.1.1 = 1 := congrArg Subtype.val h
    have h2 : cu k.1.1 = k.1.1 := inv_mul_eq_one.mp h1
    have h3 := congrArg Subtype.val h2
    rw [hcu_apply] at h3
    calc (k.1.1 : Y) * u = (u * k.1.1 * u⁻¹) * u := by rw [h3]
      _ = u * k.1.1 := by group
  let ι : κ.ker →* ↥(L ⊓ Subgroup.centralizer ({u} : Set Y)) :=
    { toFun := fun k => ⟨(k.1.1 : Y), hker k⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hι : Function.Injective ι := by
    intro a b h
    have := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext (Subtype.ext this))
  have : Group.IsSolvable κ.ker := Group.isSolvable_of_isSolvable_injective hι
  have : Group.IsSolvable M := by
    refine Group.isSolvable_of_ker_le_range κ.ker.subtype κ ?_
    intro x hx
    simpa using hx
  let f : M →* autFix ζ :=
    ((QuotientGroup.mk' (Subgroup.center L)).comp M.subtype).codRestrict (autFix ζ)
      (fun x => x.2)
  have hf : Function.Surjective f := by
    intro s
    obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective s.1
    refine ⟨⟨l, ?_⟩, Subtype.ext hl⟩
    show QuotientGroup.mk' (Subgroup.center L) l ∈ autFix ζ
    simp [hl]
  exact Group.isSolvable_of_surjective hf

structure SPLAutData (p r : ℕ) (S : Type*) [Group S] (E : Subgroup (MulAut S))
    (ζ γ : MulAut S) : Prop where
  prime_p : p.Prime
  ne_two : p ≠ 2
  prime_r : r.Prime
  dvd : r ∣ p ^ 2 + 1
  ndvd : ¬ r ∣ p ^ 2 - 1
  elem : CFSG.Open.IsElemAbelian p E
  card : Nat.card E = p ^ 4
  zeta_pow : ζ ^ p = 1
  zeta_comm : ∀ e ∈ E, ζ * e = e * ζ
  gamma_pow : ∃ k : ℕ, γ ^ r ^ k = 1
  gamma_norm : ∀ e ∈ E, γ * e * γ⁻¹ ∈ E
  gamma_zeta : γ * ζ = ζ * γ
  gamma_act : ∃ e ∈ E, γ * e * γ⁻¹ ≠ e
  solv : Group.IsSolvable ↥(autFix ζ)

open CFSG.HardMathSupport.Curtis.Proving in
theorem exists_splAutData {Y : Type} [Group Y] [Finite Y] (L : Subgroup Y) [Group.IsPerfect L]
    (p r : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hr : r.Prime) (hdvd : r ∣ p ^ 2 + 1)
    (hndvd : ¬ r ∣ p ^ 2 - 1) (u c : Y) (T X : Subgroup Y)
    (hu : u ∈ Subgroup.normalizer (L : Set Y)) (hup : u ^ p = 1)
    (hsolv : Group.IsSolvable ↥(L ⊓ Subgroup.centralizer ({u} : Set Y)))
    (hTN : T ≤ Subgroup.normalizer (L : Set Y)) (hTC : T ≤ Subgroup.centralizer ({u} : Set Y))
    (hTX : T ⊓ Subgroup.centralizer (L : Set Y) = X)
    (hcomm : ∀ a ∈ T, ∀ b ∈ T, a * b * a⁻¹ * b⁻¹ ∈ X) (hpow : ∀ a ∈ T, a ^ p ∈ X)
    (hidx : X.relIndex T = p ^ 4)
    (hcN : c ∈ Subgroup.normalizer (L : Set Y)) (hcC : c ∈ Subgroup.centralizer ({u} : Set Y))
    (hcr : ∃ k : ℕ, c ^ r ^ k = 1) (hcT : ∀ t ∈ T, c * t * c⁻¹ ∈ T)
    (hnt : ∃ t ∈ T, c * t * c⁻¹ * t⁻¹ ∉ X) :
    ∃ (E : Subgroup (MulAut (↥L ⧸ Subgroup.center ↥L))) (ζ γ : MulAut (↥L ⧸ Subgroup.center ↥L)),
      SPLAutData p r (↥L ⧸ Subgroup.center ↥L) E ζ γ := by
  set α := automizer L with hα
  let β : T →* MulAut (↥L ⧸ Subgroup.center ↥L) := α.comp (Subgroup.inclusion hTN)
  have hβ : ∀ t : T, β t = α ⟨(t : Y), hTN t.2⟩ := fun t => rfl
  have hkerβ : ∀ t : T, β t = 1 ↔ (t : Y) ∈ X := by
    intro t
    rw [hβ, automizer_eq_one_iff L ⟨(t : Y), hTN t.2⟩]
    constructor
    · intro h
      rw [← hTX]
      exact ⟨t.2, h⟩
    · intro h
      rw [← hTX] at h
      exact h.2
  have hker : β.ker = X.subgroupOf T := by
    ext t
    rw [MonoidHom.mem_ker, hkerβ, Subgroup.mem_subgroupOf]
  have hmemC : ∀ x : Y, x ∈ Subgroup.centralizer ({u} : Set Y) → x * u = u * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp hx
  have hcommβ : ∀ a b : T, β a * β b = β b * β a := by
    intro a b
    have h : β (a * b * a⁻¹ * b⁻¹) = 1 := by
      rw [hkerβ]
      exact hcomm a a.2 b b.2
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h
    exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h)
  have hpowβ : ∀ a : T, β a ^ p = 1 := by
    intro a
    rw [← map_pow, hkerβ]
    exact hpow a a.2
  have hE : CFSG.Open.IsElemAbelian p β.range := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a, ha⟩ := x.2
      obtain ⟨b, hb⟩ := y.2
      apply Subtype.ext
      change (x : MulAut (↥L ⧸ Subgroup.center ↥L)) * y = y * x
      rw [← ha, ← hb]
      exact hcommβ a b
    · obtain ⟨a, rfl⟩ := hx
      exact hpowβ a
  have hcard : Nat.card β.range = p ^ 4 := by
    rw [← hidx, ← card_quotient_eq_relIndex T X, ← hker]
    exact (Nat.card_congr (QuotientGroup.quotientKerEquivRange β).toEquiv).symm
  refine ⟨β.range, α ⟨u, hu⟩, α ⟨c, hcN⟩, ?_⟩
  refine ⟨hp, hp2, hr, hdvd, hndvd, hE, hcard, ?_, ?_, ?_, ?_, ?_, ?_, isSolvable_autFix hu hsolv⟩
  · rw [← map_pow]
    have : (⟨u, hu⟩ : Subgroup.normalizer (L : Set Y)) ^ p = 1 :=
      Subtype.ext (by simpa using hup)
    rw [this, map_one]
  · rintro _ ⟨t, rfl⟩
    rw [hβ, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hmemC t (hTC t.2)).symm
  · obtain ⟨k, hk⟩ := hcr
    refine ⟨k, ?_⟩
    rw [← map_pow]
    have : (⟨c, hcN⟩ : Subgroup.normalizer (L : Set Y)) ^ r ^ k = 1 :=
      Subtype.ext (by simpa using hk)
    rw [this, map_one]
  · rintro _ ⟨t, rfl⟩
    refine ⟨⟨c * t * c⁻¹, hcT t t.2⟩, ?_⟩
    rw [hβ, hβ, ← map_inv, ← map_mul, ← map_mul]
    rfl
  · rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hmemC c hcC)
  · obtain ⟨t, htT, htX⟩ := hnt
    refine ⟨β ⟨t, htT⟩, ⟨⟨t, htT⟩, rfl⟩, ?_⟩
    intro heq
    apply htX
    have h1 : β ⟨c * t * c⁻¹ * t⁻¹, T.mul_mem (hcT t htT) (T.inv_mem htT)⟩ = 1 := by
      have e1 : β ⟨c * t * c⁻¹, hcT t htT⟩ = α ⟨c, hcN⟩ * β ⟨t, htT⟩ * (α ⟨c, hcN⟩)⁻¹ := by
        rw [hβ, hβ, ← map_inv, ← map_mul, ← map_mul]
        rfl
      have e2 : β ⟨c * t * c⁻¹ * t⁻¹, T.mul_mem (hcT t htT) (T.inv_mem htT)⟩ =
          β ⟨c * t * c⁻¹, hcT t htT⟩ * (β ⟨t, htT⟩)⁻¹ := by
        rw [← map_inv, ← map_mul]
        rfl
      rw [e2, e1, heq, mul_inv_cancel]
    exact (hkerβ _).mp h1

open CFSG.AGLEmbedding in
@[expose] def SPLTypeBar (p : ℕ) (S : Type) [Group S] : Prop :=
  IsClassicalTwoOrG2 S ∨ (∃ n : ℕ, Nonempty (S ≃* alternatingGroup (Fin n))) ∨
    ∃ P : Sylow p S, IsCyclic ↥(P : Subgroup S)

open CFSG.AGLEmbedding in
theorem splTypeBar_of_blockType {Y : Type} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime)
    {L : Subgroup Y} (h : IsSPLBlockType p L) : SPLTypeBar p (↥L ⧸ Subgroup.center ↥L) := by
  rcases h with h | h | ⟨P, hP⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · have : Fact p.Prime := ⟨hp⟩
    refine Or.inr (Or.inr ⟨P.mapSurjective (QuotientGroup.mk'_surjective _), ?_⟩)
    rw [Sylow.coe_mapSurjective]
    exact isCyclic_of_surjective ((QuotientGroup.mk' (Subgroup.center ↥L)).subgroupMap (P : Subgroup L))
      (MonoidHom.subgroupMap_surjective _ _)

end CFSG.HardMathSupport.Curtis.Coordinator
