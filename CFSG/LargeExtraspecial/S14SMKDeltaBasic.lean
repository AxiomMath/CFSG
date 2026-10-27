module

public import CFSG.LargeExtraspecial.S14SMFOne

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14.SMK

open Subgroup Module CFSG.RankThree.OrthogonalInvolutions

variable {G : Type} [Group G]

section Basic

variable (S : Setting G) {g : G}

theorem mem_centralizer_of_mem_Qa {y : G} (hy : y ∈ S.Qa g) :
    y ∈ centralizer ({g * S.z * g⁻¹} : Set G) :=
  (S.conjBy g).QG_le_M hy

theorem Dl_le_Kz : S.QG ⊓ S.Qa g ≤ S.QG ⊓ centralizer ({g * S.z * g⁻¹} : Set G) :=
  fun _ hy => ⟨hy.1, mem_centralizer_of_mem_Qa S hy.2⟩

theorem Dl_le_L0 : S.QG ⊓ S.Qa g ≤ S.L0 g := fun _ hy => ⟨hy.2, S.QG_le_M hy.1⟩

theorem commutator_mem_Dl {k u : G} (hk : k ∈ S.L0 g)
    (hu : u ∈ S.QG ⊓ centralizer ({g * S.z * g⁻¹} : Set G)) :
    k * u * k⁻¹ * u⁻¹ ∈ S.QG ⊓ S.Qa g := by
  refine ⟨S.QG.mul_mem (S.conj_mem_QG hk.2 hu.1) (S.QG.inv_mem hu.1), ?_⟩
  have huT : u ∈ (S.conjBy g).M := hu.2
  have h := (S.conjBy g).conj_mem_QG huT ((S.conjBy g).QG.inv_mem hk.1)
  have e : k * u * k⁻¹ * u⁻¹ = k * (u * k⁻¹ * u⁻¹) := by group
  rw [e]
  exact (S.conjBy g).QG.mul_mem hk.1 h

variable [Finite G]

theorem z_not_mem_Qa (hxQ : g * S.z * g⁻¹ ∉ S.QG) : S.z ∉ S.Qa g := fun h =>
  SMF.conj_z_not_mem_QG S hxQ ((SME.mem_Qa_iff S g S.z).mp h)

theorem commute_of_mem_Kz_Dl (hxQ : g * S.z * g⁻¹ ∉ S.QG) {u d : G}
    (hu : u ∈ S.QG ⊓ centralizer ({g * S.z * g⁻¹} : Set G)) (hd : d ∈ S.QG ⊓ S.Qa g) :
    u * d = d * u := by
  have huT : u ∈ (S.conjBy g).M := hu.2
  have hc : u * d * u⁻¹ * d⁻¹ ∈ S.Qa g :=
    (S.conjBy g).QG.mul_mem ((S.conjBy g).conj_mem_QG huT hd.2) ((S.conjBy g).QG.inv_mem hd.2)
  rcases S.commutator_eq_one_or_z hu.1 hd.1 with h | h
  · calc u * d = u * d * u⁻¹ * d⁻¹ * (d * u) := by group
      _ = d * u := by rw [h, one_mul]
  · exact absurd (h ▸ hc) (z_not_mem_Qa S hxQ)

theorem z_not_mem_Dl (hxQ : g * S.z * g⁻¹ ∉ S.QG) : S.z ∉ S.QG ⊓ S.Qa g := fun h =>
  z_not_mem_Qa S hxQ h.2

theorem cl_injOn_Dl (hxQ : g * S.z * g⁻¹ ∉ S.QG) {d e : G} (hd : d ∈ S.QG ⊓ S.Qa g)
    (he : e ∈ S.QG ⊓ S.Qa g) (h : S.cl d = S.cl e) : d = e := by
  rcases (S.cl_eq_cl_iff hd.1 he.1).mp h with h1 | h1
  · exact h1.symm
  · exfalso
    apply z_not_mem_Dl S hxQ
    have e1 : S.z = d⁻¹ * e := by rw [h1]; group
    rw [e1]
    exact (S.QG ⊓ S.Qa g).mul_mem ((S.QG ⊓ S.Qa g).inv_mem hd) he

theorem card_clSub_Dl (hxQ : g * S.z * g⁻¹ ∉ S.QG) :
    Nat.card (S.clSub (S.QG ⊓ S.Qa g)) = Nat.card (S.QG ⊓ S.Qa g : Subgroup G) := by
  refine (Nat.card_congr (Equiv.ofBijective (fun d : (S.QG ⊓ S.Qa g : Subgroup G) =>
    (⟨S.cl d, S.cl_mem_clSub d.2 d.2.1⟩ : S.clSub (S.QG ⊓ S.Qa g))) ⟨fun d e h => ?_,
    fun v => ?_⟩)).symm
  · exact Subtype.ext (cl_injOn_Dl S hxQ d.2 e.2 (congrArg Subtype.val h))
  · obtain ⟨d, hd, -, hdv⟩ := S.mem_clSub_iff.mp v.2
    exact ⟨⟨d, hd⟩, Subtype.ext hdv⟩

end Basic

section Cent

variable [Finite G] (T : Setting G)

theorem card_QG_le_mul {α : G} (hαM : α ∈ T.M) (hαQ : α ∉ T.QG) (hα2 : α ^ 2 = 1) :
    Nat.card T.QG ≤ Nat.card (T.QG ⊓ centralizer ({α} : Set G) : Subgroup G) *
      2 ^ (finrank (ZMod 2) (T.commQt α) + 1) := by
  classical
  set C := T.QG ⊓ centralizer ({α} : Set G) with hC
  set P := T.clPre (T.commQt α) with hP
  have hPc : Nat.card P = 2 ^ (finrank (ZMod 2) (T.commQt α) + 1) := by
    rw [hP, T.card_clPre, T.card_submodule, pow_succ, mul_comm]
  have hmemP : ∀ q ∈ T.QG, q * α * q⁻¹ * α⁻¹ ∈ P := by
    intro q hq
    have hmem := T.commutator_zpowers_eq_clPre hαM hαQ hα2
    show q * α * q⁻¹ * α⁻¹ ∈ T.clPre (T.commQt α)
    rw [← hmem]
    have h := Subgroup.commutator_mem_commutator (mem_zpowers α) hq
    rw [commutatorElement_def] at h
    have h' := Subgroup.inv_mem _ h
    rwa [show (α * q * α⁻¹ * q⁻¹)⁻¹ = q * α * q⁻¹ * α⁻¹ by group] at h'
  let CQ : Subgroup T.QG := C.subgroupOf T.QG
  let f : T.QG ⧸ CQ → P := Quotient.lift (fun q : T.QG => (⟨(q : G) * α * (q : G)⁻¹ * α⁻¹,
      hmemP q q.2⟩ : P)) (by
    intro a b hab
    apply Subtype.ext
    have hab' : (a : G)⁻¹ * b ∈ C := by
      have := (QuotientGroup.leftRel_apply).mp hab
      exact mem_subgroupOf.mp this
    have hc : (a : G)⁻¹ * b * α = α * ((a : G)⁻¹ * b) :=
      mem_centralizer_singleton_iff.mp hab'.2
    show (a : G) * α * (a : G)⁻¹ * α⁻¹ = (b : G) * α * (b : G)⁻¹ * α⁻¹
    calc (a : G) * α * (a : G)⁻¹ * α⁻¹ = (a : G) * (α * ((a : G)⁻¹ * b)) * (b : G)⁻¹ * α⁻¹ := by
          group
      _ = (a : G) * ((a : G)⁻¹ * b * α) * (b : G)⁻¹ * α⁻¹ := by rw [hc]
      _ = (b : G) * α * (b : G)⁻¹ * α⁻¹ := by group)
  have hf : Function.Injective f := by
    intro a b hab
    induction a using QuotientGroup.induction_on with | H a => ?_
    induction b using QuotientGroup.induction_on with | H b => ?_
    have e : (a : G) * α * (a : G)⁻¹ * α⁻¹ = (b : G) * α * (b : G)⁻¹ * α⁻¹ :=
      congrArg Subtype.val hab
    refine QuotientGroup.eq.mpr (mem_subgroupOf.mpr ⟨?_, ?_⟩)
    · exact T.QG.mul_mem (T.QG.inv_mem a.2) b.2
    · refine mem_centralizer_singleton_iff.mpr ?_
      have e2 : (a : G) * α * (a : G)⁻¹ = (b : G) * α * (b : G)⁻¹ := by
        have := congrArg (· * α) e
        simpa using this
      push_cast
      calc ((a : G)⁻¹ * (b : G)) * α = (a : G)⁻¹ * ((b : G) * α * (b : G)⁻¹) * (b : G) := by
            group
        _ = (a : G)⁻¹ * ((a : G) * α * (a : G)⁻¹) * (b : G) := by rw [e2]
        _ = α * ((a : G)⁻¹ * (b : G)) := by group
  have h1 := Nat.card_le_card_of_injective f hf
  have h2 := CQ.card_mul_index
  rw [Subgroup.index_eq_card] at h2
  have h3 : Nat.card CQ = Nat.card C :=
    Nat.card_congr (subgroupOfEquivOfLe (inf_le_left : C ≤ T.QG)).toEquiv
  rw [← h2, h3, ← hPc]
  exact Nat.mul_le_mul_left _ h1

theorem card_centralizer_ge {α : G} (hαM : α ∈ T.M) (hαQ : α ∉ T.QG) (hα2 : α ^ 2 = 1) :
    2 ^ T.width ≤ Nat.card (T.QG ⊓ centralizer ({α} : Set G) : Subgroup G) := by
  have h := card_QG_le_mul T hαM hαQ hα2
  rw [T.card_QG_eq_card_Q, T.card_Q_eq] at h
  have hl : finrank (ZMod 2) (T.commQt α) ≤ T.width := by
    have h1 := finrank_commSpace_add_finrank_fixSpace (T.ρ ⟨α, hαM⟩ : T.Qt ≃ₗ[ZMod 2] T.Qt)
    rw [← T.fixQt_of_mem hαM, ← T.commQt_of_mem hαM, T.finrank_Qt_eq_two_mul_width] at h1
    have h2 := Submodule.finrank_mono (T.commQt_le_fixQt hαM hα2)
    omega
  have h4 : 2 ^ (1 + 2 * T.width) = (2 ^ T.width * 2 ^ (T.width - finrank (ZMod 2) (T.commQt α))) *
      2 ^ (finrank (ZMod 2) (T.commQt α) + 1) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  rw [h4] at h
  have h5 := Nat.le_of_mul_le_mul_right h (by positivity)
  exact le_trans (Nat.le_mul_of_pos_right _ (by positivity)) h5

end Cent

end CFSG.LargeExtraspecial.S14.SMK
