module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeZStd

public section

namespace CFSG.ComponentClassification.GrSLit.HeZ

open CFSG Subgroup

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem comm_centralizer (L : Subgroup X) :
    ∀ l ∈ L, ∀ c ∈ centralizer (L : Set X), l * c = c * l :=
  fun l hl _c hc => mem_centralizer_iff.mp hc l hl

omit [Finite X] in
theorem inf_centralizer_eq_bot {L : Subgroup X} (hZ : center ↥L = ⊥) :
    L ⊓ centralizer (L : Set X) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxL, hxC⟩ := mem_inf.mp hx
  have h : (⟨x, hxL⟩ : ↥L) ∈ center ↥L := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_centralizer_iff.mp hxC g g.2)
  rw [hZ, mem_bot] at h
  exact (mem_bot).mpr (congrArg Subtype.val h)

variable {L : Subgroup X} (hZ : center ↥L = ⊥) {Q : Subgroup X}
  (hQ : Q ≤ L ⊔ centralizer (L : Set X))

@[expose] noncomputable def fstHom : ↥Q →* ↥L :=
  (MonoidHom.fst _ _).comp (decomp (hc := comm_centralizer L) (inf_centralizer_eq_bot hZ) hQ)

@[expose] noncomputable def projL : Subgroup X := (fstHom hZ hQ).range.map L.subtype

omit [Finite X] in
theorem projL_le : projL hZ hQ ≤ L := map_subtype_le _

omit [Finite X] in
theorem fstHom_inv_mul_mem (q : ↥Q) :
    ((fstHom hZ hQ q : ↥L) : X)⁻¹ * q ∈ centralizer (L : Set X) := by
  have h := decomp_spec (hc := comm_centralizer L) (inf_centralizer_eq_bot hZ) hQ q
  have e : (fstHom hZ hQ q : ↥L) =
      (decomp (hc := comm_centralizer L) (inf_centralizer_eq_bot hZ) hQ q).1 := rfl
  rw [e, ← h, inv_mul_cancel_left]
  exact (decomp (hc := comm_centralizer L) (inf_centralizer_eq_bot hZ) hQ q).2.2

omit [Finite X] in
theorem mem_ker_fstHom_iff (q : ↥Q) :
    q ∈ (fstHom hZ hQ).ker ↔ (q : X) ∈ centralizer (L : Set X) := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    have h1 := fstHom_inv_mul_mem hZ hQ q
    rwa [h, OneMemClass.coe_one, inv_one, one_mul] at h1
  · intro h
    have h1 := fstHom_inv_mul_mem hZ hQ q
    have h2 : ((fstHom hZ hQ q : ↥L) : X) ∈ L ⊓ centralizer (L : Set X) := by
      refine mem_inf.mpr ⟨(fstHom hZ hQ q).2, ?_⟩
      have := mul_mem h (inv_mem h1)
      rwa [mul_inv_rev, inv_inv, mul_inv_cancel_left] at this
    rw [inf_centralizer_eq_bot hZ, mem_bot] at h2
    exact Subtype.ext h2

omit [Finite X] in
theorem card_projL_mul :
    Nat.card (projL hZ hQ) * Nat.card ↥(Q ⊓ centralizer (L : Set X)) = Nat.card Q := by
  have h1 := card_eq_card_quotient_mul_card_subgroup (fstHom hZ hQ).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (fstHom hZ hQ)).toEquiv] at h1
  have h2 : Nat.card (projL hZ hQ) = Nat.card (fstHom hZ hQ).range :=
    card_map_of_injective L.subtype_injective
  have h3 : Nat.card ↥(Q ⊓ centralizer (L : Set X)) = Nat.card (fstHom hZ hQ).ker := by
    have e : ((fstHom hZ hQ).ker).map Q.subtype = Q ⊓ centralizer (L : Set X) := by
      ext x
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact mem_inf.mpr ⟨q.2, (mem_ker_fstHom_iff hZ hQ q).mp hq⟩
      · intro hx
        obtain ⟨hxQ, hxC⟩ := mem_inf.mp hx
        exact ⟨⟨x, hxQ⟩, (mem_ker_fstHom_iff hZ hQ ⟨x, hxQ⟩).mpr hxC, rfl⟩
    rw [← e, card_map_of_injective Q.subtype_injective]
  rw [h2, h3, h1, mul_comm]

omit [Finite X] in
theorem projL_perfect (hP : ⁅Q, Q⁆ = Q) : ⁅projL hZ hQ, projL hZ hQ⁆ = projL hZ hQ := by
  have : Group.IsPerfect ↥Q := isPerfect_iff.mpr hP
  have hR : Group.IsPerfect ↥(fstHom hZ hQ).range :=
    Group.IsPerfect.ofSurjective (f := (fstHom hZ hQ).rangeRestrict)
      (fstHom hZ hQ).rangeRestrict_surjective
  have e : Group.IsPerfect ↥(projL hZ hQ) :=
    Group.IsPerfect.ofSurjective (f := ((fstHom hZ hQ).range.equivMapOfInjective L.subtype
      L.subtype_injective).toMonoidHom) (MulEquiv.surjective _)
  exact isPerfect_iff.mp e

omit [Finite X] in
theorem projL_le_centralizer {u : X} (hu : u ∈ L) (hQu : Q ≤ centralizer ({u} : Set X)) :
    projL hZ hQ ≤ centralizer ({u} : Set X) := by
  rintro _ ⟨_, ⟨q, rfl⟩, rfl⟩
  rw [mem_centralizer_singleton_iff]
  set l : X := ((fstHom hZ hQ q : ↥L) : X)
  have hc := fstHom_inv_mul_mem hZ hQ q
  have hqu := mem_centralizer_singleton_iff.mp (hQu q.2)
  have hcu : u * (l⁻¹ * q) = (l⁻¹ * q) * u := (mem_centralizer_iff.mp hc u hu)
  show l * u = u * l
  calc l * u = l * u * (l⁻¹ * q) * (l⁻¹ * q)⁻¹ := by group
    _ = l * ((l⁻¹ * q) * u) * (l⁻¹ * q)⁻¹ := by rw [mul_assoc l u, hcu]
    _ = q * u * (l⁻¹ * q)⁻¹ := by group
    _ = u * q * (l⁻¹ * q)⁻¹ := by rw [hqu]
    _ = u * l := by group

omit [Finite X] in
theorem comm_of_mem_projL {t : X} (htN : t ∈ normalizer (L : Set X))
    (htQ : ∀ q ∈ Q, t * q = q * t) {l : X} (hl : l ∈ projL hZ hQ) : t * l = l * t := by
  obtain ⟨_, ⟨q, rfl⟩, rfl⟩ := hl
  set l : X := ((fstHom hZ hQ q : ↥L) : X) with hldef
  set c : X := l⁻¹ * q with hcdef
  have hc : c ∈ centralizer (L : Set X) := fstHom_inv_mul_mem hZ hQ q
  have hlL : l ∈ L := (fstHom hZ hQ q).2
  have htC : t ∈ normalizer (centralizer (L : Set X) : Set X) :=
    HeEnd.normalizer_le_normalizer_centralizer L htN
  have h1 : t * l * t⁻¹ ∈ L := (mem_normalizer_iff.mp htN l).mp hlL
  have h2 : t * c * t⁻¹ ∈ centralizer (L : Set X) := (mem_normalizer_iff.mp htC c).mp hc
  have hq : (q : X) = l * c := by rw [hcdef]; group
  have htq : t * q * t⁻¹ = q := by rw [htQ q q.2, mul_inv_cancel_right]
  have hcomm : (t * l * t⁻¹) * (t * c * t⁻¹) = l * c :=
    calc (t * l * t⁻¹) * (t * c * t⁻¹) = t * (l * c) * t⁻¹ := by group
      _ = t * q * t⁻¹ := by rw [← hq]
      _ = q := htq
      _ = l * c := hq
  have h3 : l⁻¹ * (t * l * t⁻¹) = c * (t * c * t⁻¹)⁻¹ := by
    have e1 : l⁻¹ * (t * l * t⁻¹) * (t * c * t⁻¹) = c := by
      rw [mul_assoc, hcomm, inv_mul_cancel_left]
    calc l⁻¹ * (t * l * t⁻¹) = l⁻¹ * (t * l * t⁻¹) * (t * c * t⁻¹) * (t * c * t⁻¹)⁻¹ := by
          group
      _ = c * (t * c * t⁻¹)⁻¹ := by rw [e1]
  have h4 : l⁻¹ * (t * l * t⁻¹) ∈ L ⊓ centralizer (L : Set X) :=
    mem_inf.mpr ⟨mul_mem (inv_mem hlL) h1, h3 ▸ mul_mem hc (inv_mem h2)⟩
  rw [inf_centralizer_eq_bot hZ, mem_bot] at h4
  have h5 : t * l * t⁻¹ = l := by
    rw [← mul_left_cancel_iff (a := l⁻¹), h4, inv_mul_cancel]
  calc t * l = t * l * t⁻¹ * t := by group
    _ = l * t := by rw [h5]

@[expose] noncomputable def sndHom : ↥Q →* ↥(centralizer (L : Set X)) :=
  (MonoidHom.snd _ _).comp (decomp (hc := comm_centralizer L) (inf_centralizer_eq_bot hZ) hQ)

omit [Finite X] in
theorem fstHom_mul_sndHom (q : ↥Q) :
    ((fstHom hZ hQ q : ↥L) : X) * (sndHom hZ hQ q : X) = q :=
  decomp_spec (hc := comm_centralizer L) (inf_centralizer_eq_bot hZ) hQ q

omit [Finite X] in
theorem mem_ker_sndHom_iff (q : ↥Q) : q ∈ (sndHom hZ hQ).ker ↔ (q : X) ∈ L := by
  rw [MonoidHom.mem_ker]
  have h := fstHom_mul_sndHom hZ hQ q
  constructor
  · intro h1
    rw [h1, OneMemClass.coe_one, mul_one] at h
    rw [← h]
    exact (fstHom hZ hQ q).2
  · intro hq
    have h2 : (sndHom hZ hQ q : X) ∈ L ⊓ centralizer (L : Set X) := by
      refine mem_inf.mpr ⟨?_, (sndHom hZ hQ q).2⟩
      have : (sndHom hZ hQ q : X) = ((fstHom hZ hQ q : ↥L) : X)⁻¹ * q := by
        rw [← h, inv_mul_cancel_left]
      rw [this]
      exact mul_mem (inv_mem (fstHom hZ hQ q).2) hq
    rw [inf_centralizer_eq_bot hZ, mem_bot] at h2
    exact Subtype.ext h2

end CFSG.ComponentClassification.GrSLit.HeZ
