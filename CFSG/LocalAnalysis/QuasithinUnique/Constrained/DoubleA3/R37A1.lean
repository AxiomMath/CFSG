module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma36Cent
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.R37Mixed

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup

variable {G : Type} [Group G] [Finite G] {T M H S L K : Subgroup G} {s x z₁ z₂ : G}

@[expose] def blockA1 (L : Subgroup G) (s x : G) : Subgroup G :=
  blockU2 L s ⊔ conjR (blockU L) x

omit [Finite G] in
theorem le_normalizer_conjR {R X : Subgroup G} {g : G} (hg : g ∈ normalizer (R : Set G))
    (hR : R ≤ normalizer (X : Set G)) : R ≤ normalizer (conjR X g : Set G) := by
  intro r hr
  have hr' : g * r * g⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hg r).mp hr
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [mem_conjR, mem_conjR]
  have e : g * (r * y * r⁻¹) * g⁻¹ = (g * r * g⁻¹) * (g * y * g⁻¹) * (g * r * g⁻¹)⁻¹ := by group
  rw [e]
  exact Subgroup.mem_normalizer_iff.mp (hR hr') (g * y * g⁻¹)

theorem mem_normalizer_of_conj_mem {A : Subgroup G} {y : G} (h : ∀ a ∈ A, y * a * y⁻¹ ∈ A) :
    y ∈ normalizer (A : Set G) := by
  have hle : A.map (MulAut.conj y).toMonoidHom ≤ A := by
    rintro _ ⟨a, ha, rfl⟩
    exact h a ha
  have heq : A.map (MulAut.conj y).toMonoidHom = A :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj y).injective])
  rw [Subgroup.mem_normalizer_iff]
  intro a
  refine ⟨h a, fun ha => ?_⟩
  have : y * a * y⁻¹ ∈ A.map (MulAut.conj y).toMonoidHom := by rw [heq]; exact ha
  obtain ⟨a', ha', hae⟩ := this
  have : a' = a := by
    have h1 : y * a' * y⁻¹ = y * a * y⁻¹ := hae
    simpa using h1
  rw [← this]
  exact ha'

section TR

variable (hD : AppC.C56DoubleA3) (h27_1 : Lemma2_4_27_1A3) (hK : A3A3K T M H S L s x z₁ z₂ K)
include hD h27_1 hK

theorem A3A3K.comm_mod_baum : ∀ g ∈ T, ∀ h ∈ T, g⁻¹ * h⁻¹ * g * h ∈ baum S := by
  have hcs := hK.cs
  have hB := basic31 hD h27_1 hK.toA3A3
  have hRT : baum S ≤ T := (inf_le_left : baum S ≤ S).trans hcs.le_T
  have hTN : T ≤ normalizer (baum S : Set G) := fun g hg =>
    normalizer_le_normalizer_baum S (normalizer_of_relIndex_two hcs.le_T hB.idx_T hg)
  have hnorm : ((baum S).subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRT).mpr hTN
  have hcard : Nat.card (↥T ⧸ (baum S).subgroupOf T) = 2 ^ 2 := by
    have h1 : Nat.card (↥T ⧸ (baum S).subgroupOf T) = (baum S).relIndex T := rfl
    have h2 := C5.card_eq_card_mul_relIndex hRT
    have hpos : 0 < Nat.card (baum S) := Nat.card_pos
    have h3 : Nat.card (baum S) * (baum S).relIndex T = Nat.card (baum S) * 4 := by
      rw [← h2, hB.card_T]
      ring
    rw [h1, Nat.eq_of_mul_eq_mul_left hpos h3]
    norm_num
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm := (IsPGroup.isMulCommutative_of_card_eq_prime_sq hcard).is_comm.comm
  intro g hg h hh
  have h1 : (QuotientGroup.mk (⟨h, hh⟩ * ⟨g, hg⟩ : ↥T) : ↥T ⧸ (baum S).subgroupOf T) =
      QuotientGroup.mk (⟨g, hg⟩ * ⟨h, hh⟩ : ↥T) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
    exact hcomm _ _
  have h2 := Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp h1)
  simpa [mul_assoc] using h2

end TR

section A1

variable (hD : AppC.C56DoubleA3) (h27_1 : Lemma2_4_27_1A3) (hK : A3A3K T M H S L s x z₁ z₂ K)
include hD h27_1 hK

theorem A3A3K.sq_x_mem : x * x ∈ baum S := by
  have hidx := hK.relIndex_baum_sOne hD h27_1
  have hxS₁ : x ∈ sOne S x := mem_sup_right (Subgroup.mem_zpowers x)
  have hxR : x ∉ baum S := fun h => hK.x_not_mem ((inf_le_left : baum S ≤ S) h)
  exact mul_self_mem_of_relIndex_two hidx hxS₁ hxR

theorem A3A3K.w_mem : x⁻¹ * s * x * s ∈ baum S := by
  have hB := basic31 hD h27_1 hK.toA3A3
  have hcs := hK.cs
  have hs : s ∈ T := hcs.le_T hK.s_mem
  have h1 := hK.comm_mod_baum hD h27_1 x hK.x_mem s⁻¹ (inv_mem hs)
  have h2 : s * s ∈ baum S := (s_mul_self_mem_baum hB hK.toA3A3).2
  have := mul_mem h1 h2
  simpa [mul_assoc] using this

theorem A3A3K.blockUx_le_rK : conjR (blockU L) x ≤ baum S ⊓ K := by
  have hB := basic31 hD h27_1 hK.toA3A3
  have hxN : x ∈ normalizer (baum S : Set G) := hK.toA3A3x.x_mem_normalizer_baum hB
  have hxG₂ : x ∈ centralizerElem z₂ := Subgroup.mem_centralizer_singleton_iff.mpr hK.x_comm₂
  have hxK : x ∈ normalizer (K : Set G) := hK.K_norm hxG₂
  have hUK : blockU L ≤ K := hK.isA4.le.trans hK.L_le_K
  have hUB : blockU L ≤ baum S := blockU_le_baum hK.cs hK.a3
  exact le_inf ((C5.conjSubgroup_mono hUB x).trans (le_of_eq (C5.conjSubgroup_eq_self hxN)))
    ((C5.conjSubgroup_mono hUK x).trans (le_of_eq (C5.conjSubgroup_eq_self hxK)))

omit hD h27_1 in
theorem A3A3K.blockU2_le_rKs : blockU2 L s ≤ conjR (baum S ⊓ K) s := by
  have hUK : blockU L ≤ K := hK.isA4.le.trans hK.L_le_K
  have hUB : blockU L ≤ baum S := blockU_le_baum hK.cs hK.a3
  exact C5.conjSubgroup_mono (le_inf hUB hUK) s

omit hD h27_1 in
theorem A3A3K.baum_le_normalizer_blockU2 : baum S ≤ normalizer (blockU2 L s : Set G) :=
  le_normalizer_conjR (mem_normalizer_baum hK.s_mem) (baum_le_normalizer_blockU hK.cs hK.a3)

theorem A3A3K.baum_le_normalizer_blockUx :
    baum S ≤ normalizer (conjR (blockU L) x : Set G) := by
  have hB := basic31 hD h27_1 hK.toA3A3
  exact le_normalizer_conjR (hK.toA3A3x.x_mem_normalizer_baum hB)
    (baum_le_normalizer_blockU hK.cs hK.a3)

theorem A3A3K.baum_le_normalizer_blockA1 :
    baum S ≤ normalizer (blockA1 L s x : Set G) := fun _ hr =>
  C1.mem_normalizer_sup (hK.baum_le_normalizer_blockU2 hr)
    (hK.baum_le_normalizer_blockUx hD h27_1 hr)

theorem A3A3K.mul_xs_mem_normalizer_blockA1
    (hcomm : ∀ a ∈ blockU2 L s, ∀ b ∈ conjR (blockU L) x, a * b = b * a) :
    x * s ∈ normalizer (blockA1 L s x : Set G) := by
  have hB := basic31 hD h27_1 hK.toA3A3
  have hxx := hK.sq_x_mem hD h27_1
  have hw := hK.w_mem hD h27_1
  have hUnorm := baum_le_normalizer_blockU hK.cs hK.a3
  have hUxnorm := hK.baum_le_normalizer_blockUx hD h27_1
  have ha : ∀ v ∈ blockU2 L s, x * s * v * (x * s)⁻¹ ∈ conjR (blockU L) x := by
    intro v hv
    have hsv : s * v * s⁻¹ ∈ blockU L := mem_conjR.mp hv
    rw [mem_conjR]
    have e : x * (x * s * v * (x * s)⁻¹) * x⁻¹ = (x * x) * (s * v * s⁻¹) * (x * x)⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hUnorm hxx) _).mp hsv
  have hb : ∀ c ∈ conjR (blockU L) x, x * s * c * (x * s)⁻¹ ∈ blockU2 L s := by
    intro c hc
    show x * s * c * (x * s)⁻¹ ∈ conjR (blockU L) s
    rw [mem_conjR]
    have hwc : (x⁻¹ * s * x * s) * c * (x⁻¹ * s * x * s)⁻¹ ∈ conjR (blockU L) x :=
      (Subgroup.mem_normalizer_iff.mp (hUxnorm hw) c).mp hc
    have hxu : x * ((x⁻¹ * s * x * s) * c * (x⁻¹ * s * x * s)⁻¹) * x⁻¹ ∈ blockU L :=
      mem_conjR.mp hwc
    have e : s * (x * s * c * (x * s)⁻¹) * s⁻¹ =
        x * ((x⁻¹ * s * x * s) * c * (x⁻¹ * s * x * s)⁻¹) * x⁻¹ := by group
    rw [e]
    exact hxu
  apply mem_normalizer_of_conj_mem
  intro a haA
  obtain ⟨v, hv, c, hc, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm haA
  have e : x * s * (v * c) * (x * s)⁻¹ =
      (x * s * v * (x * s)⁻¹) * (x * s * c * (x * s)⁻¹) := by group
  rw [e]
  exact mul_mem (mem_sup_right (ha v hv)) (mem_sup_left (hb c hc))

theorem A3A3K.blockA1_card
    (hbot : (baum S ⊓ K) ⊓ conjR (baum S ⊓ K) s = ⊥)
    (hcomm : ∀ a ∈ baum S ⊓ K, ∀ b ∈ conjR (baum S ⊓ K) s, a * b = b * a) :
    IsElemAbelian 2 (blockA1 L s x) ∧ Nat.card (blockA1 L s x) = 16 := by
  have hUx := hK.blockUx_le_rK hD h27_1
  have hU2 := hK.blockU2_le_rKs
  have hc : ∀ a ∈ blockU2 L s, ∀ b ∈ conjR (blockU L) x, a * b = b * a := fun a ha b hb =>
    (hcomm b (hUx hb) a (hU2 ha)).symm
  have hAb := isElemAbelian_sup_of_commute hK.isA4s.isElemAbelian_U
    (isElemAbelian_conjR hK.isA4.isElemAbelian_U x) hc
  refine ⟨hAb, ?_⟩
  have hN : blockU2 L s ≤ normalizer (conjR (blockU L) x : Set G) := C5.le_normalizer_of_commute hc
  have hinf : blockU2 L s ⊓ conjR (blockU L) x = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    have : g ∈ (baum S ⊓ K) ⊓ conjR (baum S ⊓ K) s := ⟨hUx hg.2, hU2 hg.1⟩
    rw [hbot] at this
    exact this
  have h1 := C5.card_sup_mul_card_inf_of_le_normalizer hN
  have hc1 : Nat.card (blockU2 L s) = 4 := hK.isA4s.card_U
  have hc2 : Nat.card (conjR (blockU L) x) = 4 := (hK.isA4.conj x).card_U
  rw [hinf, Subgroup.card_bot, hc1, hc2] at h1
  show Nat.card ↥(blockU2 L s ⊔ conjR (blockU L) x) = 16
  omega

omit hD h27_1 in
theorem A3A3K.z_mem_blockA1 : z₁ * z₂ ∈ blockA1 L s x := by
  have hz₂ : z₂ ∈ blockU2 L s := hK.toA3A3x.z₂_mem.1
  have hz₁ : z₁ ∈ conjR (blockU L) x := by
    rw [mem_conjR]
    have : x * z₁ * x⁻¹ = z₁ := by
      calc x * z₁ * x⁻¹ = z₁ * x * x⁻¹ := by rw [hK.x_comm₁]
        _ = z₁ := by group
    rw [this]
    exact hK.toA3A3x.z₁_mem.1
  exact mul_mem (mem_sup_right hz₁) (mem_sup_left hz₂)

theorem A3A3K.Ls_le_normalizer_blockA1
    (hcomm : ∀ a ∈ baum S ⊓ K, ∀ b ∈ conjR (baum S ⊓ K) s, a * b = b * a) :
    conjR L s ≤ normalizer (blockA1 L s x : Set G) := by
  have hUx := hK.blockUx_le_rK hD h27_1
  have hU2 := hK.blockU2_le_rKs
  have hAs := hK.isA4s
  have hB := basic31 hD h27_1 hK.toA3A3
  have hRL : baum S ≤ normalizer (conjR L s : Set G) :=
    le_normalizer_conjR (mem_normalizer_baum hK.s_mem) (fun r hr => by
      have : r ∈ S ⊓ normalizer (L : Set G) := by rw [hB.N_eq]; exact hr
      exact this.2)
  have key : ∀ l ∈ conjR L s, ∀ c ∈ conjR (blockU L) x, l * c * l⁻¹ ∈ blockA1 L s x := by
    intro l hl c hc
    have hcR : c ∈ baum S := (hUx hc).1
    obtain ⟨u, hu, hlu⟩ := hAs.exists_inner (hRL hcR) (fun v hv =>
      hcomm c (hUx hc) v (hU2 hv))
    have h1 := hlu l⁻¹ (inv_mem hl)
    have hmem : l * u * l⁻¹ * u⁻¹ ∈ blockU2 L s :=
      mul_mem ((Subgroup.mem_normalizer_iff.mp (hAs.le_normalizer hl) u).mp hu) (inv_mem hu)
    have e : l * c * l⁻¹ = (l * u * l⁻¹ * u⁻¹) * c := by
      calc l * c * l⁻¹ = l * (c * l⁻¹ * c⁻¹) * c := by group
        _ = l * (u * l⁻¹ * u⁻¹) * c := by rw [h1]
        _ = (l * u * l⁻¹ * u⁻¹) * c := by group
    rw [e]
    exact mul_mem (mem_sup_left hmem) (mem_sup_right hc)
  have hc : ∀ a ∈ blockU2 L s, ∀ b ∈ conjR (blockU L) x, a * b = b * a := fun a ha b hb =>
    (hcomm b (hUx hb) a (hU2 ha)).symm
  intro l hl
  apply mem_normalizer_of_conj_mem
  intro a ha
  obtain ⟨v, hv, c, hc', rfl⟩ := exists_mul_of_mem_sup_of_commute hc ha
  have e : l * (v * c) * l⁻¹ = (l * v * l⁻¹) * (l * c * l⁻¹) := by group
  rw [e]
  refine mul_mem (mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hAs.le_normalizer hl) v).mp hv))
    (key l hl c hc')

end A1

end CFSG.QuasithinUnique.DoubleA3
