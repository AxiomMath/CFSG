module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddCtrlDefs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddDefs
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddCtrlBasic
import CFSG.GH74.Generic.S1.KL3Red
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Closing.Lift

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup

variable {G : Type} [Group G] [Finite G] {A V K : Subgroup G} {y : G}

omit [Finite G] in
private theorem commutator_map_subgroupOf_mk'_eq (hKA : K ≤ A) (hK : ⁅K, K⁆ = K) :
    ⁅(K.subgroupOf A).map (QuotientGroup.mk' (center ↥A)),
        (K.subgroupOf A).map (QuotientGroup.mk' (center ↥A))⁆ =
      (K.subgroupOf A).map (QuotientGroup.mk' (center ↥A)) := by
  rw [← Subgroup.map_commutator]
  congr 1
  apply Subgroup.map_injective A.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKA, hK]

omit [Finite G] in
private theorem map_subgroupOf_le_centralizer_mk' {u : G} (hKu : K ≤ centralizer ({u} : Set G))
    (huA : u ∈ A) :
    (K.subgroupOf A).map (QuotientGroup.mk' (center ↥A)) ≤
      centralizer ({QuotientGroup.mk' (center ↥A) ⟨u, huA⟩} : Set (↥A ⧸ center ↥A)) := by
  intro l hl
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hl
  have hku : (k : G) * u = u * (k : G) := by
    have h :=
      (Subgroup.mem_centralizer_iff.1 (hKu (Subgroup.mem_subgroupOf.1 hk))) u (by simp)
    exact h.symm
  have hcomm : k * ⟨u, huA⟩ = ⟨u, huA⟩ * k := by
    ext
    exact hku
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  subst hz
  rw [← map_mul, ← map_mul, hcomm]

omit [Finite G] in
private theorem mk'_ne_one_of_odd_center (hodd : Odd (Nat.card (center ↥A))) {v : G}
    (hvA : v ∈ A) (hv2 : v * v = 1) (hv1 : v ≠ 1) :
    QuotientGroup.mk' (center ↥A) ⟨v, hvA⟩ ≠ 1 := by
  intro h1
  have hcent : (⟨v, hvA⟩ : ↥A) ∈ center ↥A := by
    rw [← QuotientGroup.eq_one_iff]
    exact h1
  have hsq : (⟨v, hvA⟩ : ↥A) * ⟨v, hvA⟩ = 1 := by
    simpa [pow_two] using hv2
  have hone : (⟨v, hvA⟩ : ↥A) = 1 :=
    CFSG.EvenSporadicStandard.Induction.Closing.eq_one_of_sq_eq_one_of_odd_center
      hodd hcent hsq
  apply hv1
  have hval := congrArg Subtype.val hone
  simpa using hval

omit [Finite G] in
private theorem conj_eq_mul_of_mk'_eq (hodd : Odd (Nat.card (center ↥A))) {a u v : ↥A}
    (hu : u * u = 1) (hv : v * v = 1) (hc : u * v = v * u)
    (h : ((a * u * a⁻¹ : ↥A) : ↥A ⧸ center ↥A) = ((u * v : ↥A) : ↥A ⧸ center ↥A)) :
    a * u * a⁻¹ = u * v := by
  have hx : (a * u * a⁻¹) * (a * u * a⁻¹) = 1 := by
    change (MulAut.conj a) u * (MulAut.conj a) u = 1
    rw [← map_mul, hu, map_one]
  have hy : (u * v) * (u * v) = 1 := by
    calc u * v * (u * v) = u * (v * u) * v := by group
      _ = u * (u * v) * v := by rw [← hc]
      _ = u * u * (v * v) := by group
      _ = 1 := by rw [hu, hv, mul_one]
  exact CFSG.EvenSporadicStandard.Induction.Closing.eq_of_mk_eq_of_sq hodd hx hy h

omit [Finite G] in
private theorem exists_a_bar_of_l34SuzOddData (hSG : SuzTwoBFusionGeneration)
    (hsuz : Blueprint.NativeSporadic.IsSporadic (↥A ⧸ center ↥A) .Suz)
    (hodd : Odd (Nat.card (center ↥A))) (hD : L34SuzOddData A V K y) {u : G} (hu : u ∈ V)
    (hu1 : u ≠ 1) {v : G} (hv : v ∈ K) (hv2 : v * v = 1) (hv1 : v ≠ 1) :
    ∃ a_bar : ↥A ⧸ center ↥A,
      a_bar * QuotientGroup.mk' (center ↥A) ⟨u, hD.le_A hu⟩ * a_bar⁻¹ =
          QuotientGroup.mk' (center ↥A) ⟨u, hD.le_A hu⟩ *
            QuotientGroup.mk' (center ↥A) ⟨v, le_A_of_l34SuzOddData hD hv⟩ ∧
        (K.subgroupOf A).map (QuotientGroup.mk' (center ↥A)) ⊔
            ((K.subgroupOf A).map (QuotientGroup.mk' (center ↥A))).map
                (MulAut.conj a_bar).toMonoidHom =
          ⊤ := by
  let x : ↥A ⧸ center ↥A := QuotientGroup.mk' (center ↥A) ⟨u, hD.le_A hu⟩
  let L : Subgroup (↥A ⧸ center ↥A) := (K.subgroupOf A).map (QuotientGroup.mk' (center ↥A))
  let h : ↥A ⧸ center ↥A :=
    QuotientGroup.mk' (center ↥A) ⟨v, le_A_of_l34SuzOddData hD hv⟩
  have hKA : K ≤ A := le_A_of_l34SuzOddData hD
  have hKu : K ≤ centralizer ({u} : Set G) := le_centralizer_of_l34SuzOddData hD hu
  have huA : u ∈ A := hD.le_A hu
  have hvA : v ∈ A := hKA hv
  have hx2 : x * x = 1 := by
    dsimp only [x]
    rw [← map_mul, ← map_one (QuotientGroup.mk' (center ↥A))]
    congr 1
    ext
    exact hD.mul_self u hu
  have hxC : Nat.card (centralizer ({x} : Set (↥A ⧸ center ↥A))) = 161280 := by
    dsimp only [x]
    exact hD.card_centralizer u hu hu1
  have hLC : L ≤ centralizer ({x} : Set (↥A ⧸ center ↥A)) := by
    dsimp only [L, x]
    exact map_subgroupOf_le_centralizer_mk' hKu huA
  have hLperf : ⁅L, L⁆ = L := by
    dsimp only [L]
    exact commutator_map_subgroupOf_mk'_eq hKA hD.perfect
  have hLcard : Nat.card L = 20160 := hD.card_image
  have hh_mem : h ∈ L := by
    dsimp only [h, L]
    apply Subgroup.mem_map_of_mem
    exact Subgroup.mem_subgroupOf.2 hv
  have hh2 : h * h = 1 := by
    dsimp only [h]
    rw [← map_mul, ← map_one (QuotientGroup.mk' (center ↥A))]
    congr 1
    simpa [pow_two] using hv2
  have hh1 : h ≠ 1 := by
    dsimp only [h]
    exact mk'_ne_one_of_odd_center hodd hvA hv2 hv1
  exact hSG _ hsuz x hx2 hxC L hLC hLperf hLcard h hh_mem hh2 hh1

omit [Finite G] in
private theorem conj_eq_of_lift (hodd : Odd (Nat.card (center ↥A)))
    (hD : L34SuzOddData A V K y) {u : G} (hu : u ∈ V) {v : G} (hv : v ∈ K) (hv2 : v * v = 1)
    {a_A : ↥A} {a_bar : ↥A ⧸ center ↥A}
    (ha_A : QuotientGroup.mk' (center ↥A) a_A = a_bar)
    (hconj : a_bar * QuotientGroup.mk' (center ↥A) ⟨u, hD.le_A hu⟩ * a_bar⁻¹ =
      QuotientGroup.mk' (center ↥A) ⟨u, hD.le_A hu⟩ *
        QuotientGroup.mk' (center ↥A) ⟨v, le_A_of_l34SuzOddData hD hv⟩) :
    (a_A : G) * u * (a_A : G)⁻¹ = u * v := by
  have hKA : K ≤ A := le_A_of_l34SuzOddData hD
  have hKu : K ≤ centralizer ({u} : Set G) := le_centralizer_of_l34SuzOddData hD hu
  have huA : u ∈ A := hD.le_A hu
  have hvA : v ∈ A := hKA hv
  have hu_sq : (⟨u, huA⟩ : ↥A) * ⟨u, huA⟩ = 1 := by
    ext
    exact hD.mul_self u hu
  have hv_sq : (⟨v, hvA⟩ : ↥A) * ⟨v, hvA⟩ = 1 := by
    simpa [pow_two] using hv2
  have hcomm : (⟨u, huA⟩ : ↥A) * ⟨v, hvA⟩ = ⟨v, hvA⟩ * ⟨u, huA⟩ := by
    ext
    exact (Subgroup.mem_centralizer_iff.1 (hKu hv)) u (by simp)
  have himg : ((a_A * ⟨u, huA⟩ * a_A⁻¹ : ↥A) : ↥A ⧸ center ↥A) =
      ((⟨u, huA⟩ * ⟨v, hvA⟩ : ↥A) : ↥A ⧸ center ↥A) := by
    have h1 := hconj
    rw [← ha_A] at h1
    change QuotientGroup.mk' (center ↥A) a_A * QuotientGroup.mk' (center ↥A) ⟨u, huA⟩ *
        (QuotientGroup.mk' (center ↥A) a_A)⁻¹ =
      QuotientGroup.mk' (center ↥A) ⟨u, huA⟩ * QuotientGroup.mk' (center ↥A) ⟨v, hvA⟩
    exact h1
  have h := conj_eq_mul_of_mk'_eq hodd hu_sq hv_sq hcomm himg
  simpa using congrArg Subtype.val h

omit [Finite G] in
private theorem map_sup_map_conj_eq_top {a_A : ↥A} {a_bar : ↥A ⧸ center ↥A}
    (ha_A : QuotientGroup.mk' (center ↥A) a_A = a_bar)
    (hgen : (K.subgroupOf A).map (QuotientGroup.mk' (center ↥A)) ⊔
        ((K.subgroupOf A).map (QuotientGroup.mk' (center ↥A))).map
            (MulAut.conj a_bar).toMonoidHom =
      ⊤) :
    ((K.subgroupOf A ⊔ (K.subgroupOf A).map (MulAut.conj a_A).toMonoidHom).map
        (QuotientGroup.mk' (center ↥A))) =
      ⊤ := by
  rw [Subgroup.map_sup]
  have hcomp : (QuotientGroup.mk' (center ↥A)).comp (MulAut.conj a_A).toMonoidHom =
      (MulAut.conj a_bar).toMonoidHom.comp (QuotientGroup.mk' (center ↥A)) := by
    ext z
    change QuotientGroup.mk' (center ↥A) a_A * QuotientGroup.mk' (center ↥A) z *
        (QuotientGroup.mk' (center ↥A) a_A)⁻¹ =
      a_bar * QuotientGroup.mk' (center ↥A) z * a_bar⁻¹
    rw [ha_A]
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hgen]

omit [Finite G] in
private theorem subgroupOf_map_conj_eq_map_conj_subgroupOf (hKA : K ≤ A) (a_A : ↥A) :
    (K.map (MulAut.conj (a_A : G)).toMonoidHom).subgroupOf A =
      (K.subgroupOf A).map (MulAut.conj a_A).toMonoidHom := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨k, hk, hk_eq⟩ := Subgroup.mem_map.1 hx
    apply Subgroup.mem_map.2
    refine ⟨⟨k, hKA hk⟩, hk, ?_⟩
    ext
    exact hk_eq
  · intro hx
    obtain ⟨k, hk, hk_eq⟩ := Subgroup.mem_map.1 hx
    apply Subgroup.mem_subgroupOf.2
    apply Subgroup.mem_map.2
    refine ⟨k.val, hk, ?_⟩
    have h := congrArg Subtype.val hk_eq
    simpa [MulAut.conj_apply] using h

omit [Finite G] in
private theorem sup_map_conj_eq_of_map_eq_top (hKA : K ≤ A) (hperf : Group.IsPerfect ↥A)
    (a_A : ↥A)
    (hmap : ((K.subgroupOf A ⊔ (K.subgroupOf A).map (MulAut.conj a_A).toMonoidHom).map
        (QuotientGroup.mk' (center ↥A))) =
      ⊤) :
    K ⊔ K.map (MulAut.conj (a_A : G)).toMonoidHom = A := by
  have hKA' : K.map (MulAut.conj (a_A : G)).toMonoidHom ≤ A := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hx
    simpa [MulAut.conj_apply] using A.mul_mem (A.mul_mem a_A.2 (hKA hk)) (A.inv_mem a_A.2)
  have htop : (K.subgroupOf A ⊔ (K.subgroupOf A).map (MulAut.conj a_A).toMonoidHom) = ⊤ :=
    CFSG.GH74.Generic.S1.kl3_eq_top_of_map_eq_top hperf hmap
  have hsub : (K ⊔ K.map (MulAut.conj (a_A : G)).toMonoidHom).subgroupOf A = ⊤ := by
    rw [Subgroup.subgroupOf_sup hKA hKA',
      subgroupOf_map_conj_eq_map_conj_subgroupOf hKA a_A, htop]
  refine le_antisymm (sup_le hKA hKA') ?_
  intro x hx
  have hx' : (⟨x, hx⟩ : ↥A) ∈
      (K ⊔ K.map (MulAut.conj (a_A : G)).toMonoidHom).subgroupOf A := by
    rw [hsub]
    exact Subgroup.mem_top _
  exact hx'

omit [Finite G] in
theorem exists_conj_mul_sup_eq_of_l34SuzOddData (hSG : SuzTwoBFusionGeneration)
    (hperf : Group.IsPerfect ↥A)
    (hsuz : Blueprint.NativeSporadic.IsSporadic (↥A ⧸ center ↥A) .Suz)
    (hodd : Odd (Nat.card (center ↥A))) (hD : L34SuzOddData A V K y) {u : G} (hu : u ∈ V)
    (hu1 : u ≠ 1) {v : G} (hv : v ∈ K) (hv2 : v * v = 1) (hv1 : v ≠ 1) :
    ∃ a ∈ A, a * u * a⁻¹ = u * v ∧ K ⊔ K.map (MulAut.conj a).toMonoidHom = A := by
  obtain ⟨a_bar, ha_bar_conj, ha_bar_gen⟩ :=
    exists_a_bar_of_l34SuzOddData hSG hsuz hodd hD hu hu1 hv hv2 hv1
  obtain ⟨a_A, ha_A⟩ := QuotientGroup.mk'_surjective (center ↥A) a_bar
  refine ⟨(a_A : G), a_A.2, conj_eq_of_lift hodd hD hu hv hv2 ha_A ha_bar_conj, ?_⟩
  exact sup_map_conj_eq_of_map_eq_top (le_A_of_l34SuzOddData hD) hperf a_A
    (map_sup_map_conj_eq_top ha_A ha_bar_gen)

end CFSG.ComponentClassification.GrSLit.L34Sec5S
