module

public import CFSG.Assembly.Subnormal
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTGroup

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HSubT

open CFSG.Open
open scoped commutatorElement

theorem le_center_of_normal_ne_top {G : Type} [Group G] (hq : IsQuasisimple G) (N : Subgroup G)
    [N.Normal] (hN : N ≠ ⊤) : N ≤ Subgroup.center G := by
  set Z := Subgroup.center G with hZ
  have hQsimp : IsSimpleGroup (G ⧸ Z) := hq.2
  set M : Subgroup (G ⧸ Z) := (N ⊔ Z).map (QuotientGroup.mk' Z) with hM
  haveI : M.Normal := Subgroup.Normal.map inferInstance (QuotientGroup.mk' Z)
    (QuotientGroup.mk'_surjective Z)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M with hbot | htop
  · intro n hn
    have h1 : (QuotientGroup.mk' Z n : G ⧸ Z) ∈ M :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_sup_left hn)
    rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  · exfalso
    have hNZ : N ⊔ Z = ⊤ := by
      rw [eq_top_iff]
      intro g _
      have hg : (QuotientGroup.mk' Z g : G ⧸ Z) ∈ M := by rw [htop]; exact Subgroup.mem_top _
      obtain ⟨m, hm, hmg⟩ := Subgroup.mem_map.mp hg
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_iff_div_mem] at hmg
      have hz' : (m * g⁻¹)⁻¹ ∈ Z := Z.inv_mem (by rwa [div_eq_mul_inv] at hmg)
      have hgeq : g = (m * g⁻¹)⁻¹ * m := by group
      rw [hgeq]
      exact (N ⊔ Z).mul_mem (Subgroup.mem_sup_right hz') hm
    have hdec : ∀ a : G, ∃ n ∈ N, ∃ z ∈ Z, n * z = a := fun a => by
      have ha : a ∈ N ⊔ Z := by rw [hNZ]; exact Subgroup.mem_top a
      exact (Subgroup.mem_sup_of_normal_right).mp ha
    have hcomm : commutator G ≤ N := by
      show ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ ≤ N
      rw [Subgroup.commutator_le]
      intro a _ b _
      obtain ⟨n, hn, z, hz, rfl⟩ := hdec a
      obtain ⟨m, hm, w, hw, rfl⟩ := hdec b
      have hzc : ∀ g : G, z * g = g * z := fun g => (Subgroup.mem_center_iff.mp hz g).symm
      have hwc : ∀ g : G, w * g = g * w := fun g => (Subgroup.mem_center_iff.mp hw g).symm
      have h1 : z * (m * w) * z⁻¹ = m * w := by
        calc z * (m * w) * z⁻¹ = (z * m) * w * z⁻¹ := by group
          _ = (m * z) * w * z⁻¹ := by rw [hzc m]
          _ = m * (z * w) * z⁻¹ := by group
          _ = m * (w * z) * z⁻¹ := by rw [hzc w]
          _ = m * w := by group
      have hwn : w * n⁻¹ = n⁻¹ * w := hwc n⁻¹
      have key : ⁅n * z, m * w⁆ = n * m * n⁻¹ * m⁻¹ := by
        rw [commutatorElement_def]
        calc n * z * (m * w) * (n * z)⁻¹ * (m * w)⁻¹
            = n * (z * (m * w) * z⁻¹) * n⁻¹ * (m * w)⁻¹ := by group
          _ = n * (m * w) * n⁻¹ * (m * w)⁻¹ := by rw [h1]
          _ = n * m * (w * n⁻¹) * w⁻¹ * m⁻¹ := by group
          _ = n * m * (n⁻¹ * w) * w⁻¹ * m⁻¹ := by rw [hwn]
          _ = n * m * n⁻¹ * m⁻¹ := by group
      rw [key]
      have hc : m * n⁻¹ * m⁻¹ ∈ N := by
        have := Subgroup.Normal.conj_mem inferInstance n⁻¹ (N.inv_mem hn) m
        exact this
      have : n * m * n⁻¹ * m⁻¹ = n * (m * n⁻¹ * m⁻¹) := by group
      rw [this]
      exact N.mul_mem hn hc
    rw [hq.1] at hcomm
    exact hN (top_le_iff.mp hcomm)

theorem mem_center_of_quotQuot_eq_one {G : Type} [Group G] (hq : IsQuasisimple G) (N : Subgroup G)
    [N.Normal] (hN : N ≠ ⊤) (x : G)
    (hx : (QuotientGroup.mk (QuotientGroup.mk x : G ⧸ N) :
      (G ⧸ N) ⧸ Subgroup.center (G ⧸ N)) = 1) : x ∈ Subgroup.center G := by
  have hNZ := le_center_of_normal_ne_top hq N hN
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_center_iff] at hx
  have hw : ∀ g : G, ⁅x⁻¹, g⁆ ∈ Subgroup.center G := by
    intro g
    apply hNZ
    have h := hx (QuotientGroup.mk g⁻¹)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h
    have e : ⁅x⁻¹, g⁆ = (g⁻¹ * x)⁻¹ * (x * g⁻¹) := by
      rw [commutatorElement_def]; group
    rw [e]
    exact h
  have hx' : x⁻¹ ∈ Subgroup.center G :=
    mem_center_of_commutator_mem_center hq hw
  exact inv_mem_iff.mp hx'

theorem lift_of_inner {H : Type} [Group H] {J : Subgroup H} (hJq : IsQuasisimple ↥J)
    {T : Type} [Group T] (φ : ↥J →* T) (hφs : Function.Surjective φ)
    (hφk : ∀ x : ↥J, φ x = 1 → x ∈ Subgroup.center ↥J)
    {d : H} (c : ↥J ≃* ↥J) (hc : ∀ x : ↥J, (c x : H) = d * x * d⁻¹)
    {s : T} (hs : ∀ x : ↥J, φ (c x) = s * φ x * s⁻¹) :
    ∃ j : ↥J, ∀ x : ↥J, c x = j * x * j⁻¹ := by
  obtain ⟨j, hj⟩ := hφs s
  have hz : ∀ x : ↥J, c x * (j * x * j⁻¹)⁻¹ ∈ Subgroup.center ↥J := by
    intro x
    apply hφk
    rw [map_mul, map_inv, map_mul, map_mul, map_inv, hs x, hj]
    group
  have hmul : ∀ x y : ↥J, c (x * y) * (j * (x * y) * j⁻¹)⁻¹ =
      (c x * (j * x * j⁻¹)⁻¹) * (c y * (j * y * j⁻¹)⁻¹) := by
    intro x y
    have hcomm2 : (j * x * j⁻¹)⁻¹ * (c y * (j * y * j⁻¹)⁻¹) =
        (c y * (j * y * j⁻¹)⁻¹) * (j * x * j⁻¹)⁻¹ :=
      Subgroup.mem_center_iff.mp (hz y) _
    calc c (x * y) * (j * (x * y) * j⁻¹)⁻¹
        = c x * (c y * (j * y * j⁻¹)⁻¹) * (j * x * j⁻¹)⁻¹ := by
          rw [map_mul]; group
      _ = c x * ((c y * (j * y * j⁻¹)⁻¹) * (j * x * j⁻¹)⁻¹) := by group
      _ = c x * ((j * x * j⁻¹)⁻¹ * (c y * (j * y * j⁻¹)⁻¹)) := by rw [hcomm2]
      _ = (c x * (j * x * j⁻¹)⁻¹) * (c y * (j * y * j⁻¹)⁻¹) := by group
  let ζ : ↥J →* ↥(Subgroup.center ↥J) :=
    MonoidHom.mk' (fun x => ⟨c x * (j * x * j⁻¹)⁻¹, hz x⟩)
      (fun x y => Subtype.ext (hmul x y))
  have hker : commutator ↥J ≤ ζ.ker := by
    show ⁅(⊤ : Subgroup ↥J), (⊤ : Subgroup ↥J)⁆ ≤ ζ.ker
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp (hz a) (c b * (j * b * j⁻¹)⁻¹)).symm
  rw [hJq.1] at hker
  refine ⟨j, fun x => ?_⟩
  have hx : ζ x = 1 := by
    have := hker (Subgroup.mem_top x)
    exact this
  have hx' : c x * (j * x * j⁻¹)⁻¹ = 1 := congrArg Subtype.val hx
  exact (mul_inv_eq_one.mp hx')

theorem mem_centralizer_iff_of_conj {H : Type} [Group H] {J : Subgroup H} {d j : H}
    (hj : ∀ x ∈ J, d * x * d⁻¹ = j * x * j⁻¹) {x : H} (hx : x ∈ J) :
    x * d = d * x ↔ x * j = j * x := by
  set u : H := j⁻¹ * d with hu
  have hcomm : ∀ y ∈ J, y * u = u * y := by
    intro y hy
    have h := hj y hy
    have : u * y = y * u := by
      rw [hu]
      calc j⁻¹ * d * y = j⁻¹ * (d * y * d⁻¹) * d := by group
        _ = j⁻¹ * (j * y * j⁻¹) * d := by rw [h]
        _ = y * (j⁻¹ * d) := by group
    exact this.symm
  have hd : d = j * u := by rw [hu]; group
  constructor
  · intro h
    rw [hd] at h
    have h2 : (x * j) * u = (j * x) * u := by
      calc (x * j) * u = x * (j * u) := by group
        _ = (j * u) * x := h
        _ = j * (u * x) := by group
        _ = j * (x * u) := by rw [← hcomm x hx]
        _ = (j * x) * u := by group
    exact mul_right_cancel h2
  · intro h
    rw [hd]
    calc x * (j * u) = (x * j) * u := by group
      _ = (j * x) * u := by rw [h]
      _ = j * (x * u) := by group
      _ = j * (u * x) := by rw [hcomm x hx]
      _ = (j * u) * x := by group

theorem isComponentOf_subgroupOf {H : Type} [Group H] {J K X : Subgroup H} (hKJ : K ≤ J)
    (hK : IsComponentOf K X) : IsComponentOf (K.subgroupOf J) (X.subgroupOf J) := by
  refine ⟨fun y hy => hK.1 hy, ?_, ?_⟩
  · exact CFSG.Open.IsSubnormal.comap J.subtype hK.2.1
  · have hiso : ↥(K.subgroupOf J) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKJ
    exact (IsQuasisimple.congr hiso).mpr hK.2.2

end CFSG.LocalAnalysis.GLTheoremA.HSubT

end
