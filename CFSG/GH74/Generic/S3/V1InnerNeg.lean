module

public import CFSG.GH74.Generic.S3.V1InnerLib
public import CFSG.GH74.Generic.S3.V1InnerEps

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank Subgroup
open CFSG.GH74.KGroups.L3Eps (InvData GraphData)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.QuasithinUnique.Setup.X5 (normalizerAct normalizerAct_of_mem normalizerAct_apply_mk conjOn coe_conjOn
  mem_centralizer_of_normalizerAct_eq_one eq_one_of_involution_mem_odd)
open CFSG.GH74.KGroups.Bal (commutator_induction commutator_self_of_quasisimple balance_commute_sub)
open CFSG.GH74.Generic (exists_two_subgroup_card_ge_four)
open scoped MatrixGroups commutatorElement

section Main

variable {G : Type} [Group G] [Finite G]

theorem isSolvable_of_central_ker {H K : Type*} [Group H] [Group K] (f : H →* K)
    (hker : f.ker ≤ Subgroup.center H) (hK : Group.IsSolvable K) : Group.IsSolvable H := by
  have : Group.IsSolvable ↥(Subgroup.center H) := inferInstance
  exact Group.isSolvable_of_ker_le_range (Subgroup.center H).subtype f (by simpa using hker)

theorem Conf2A.exists_S {t : StatedLieTag} {p f : ℕ} {v w : G} {Iv Iw Ivw P : Subgroup G}
    (C : Conf2A G t p f v w Iv Iw Ivw P) {L : Subgroup G} (hIL : Iv ≤ L)
    (hodd : Odd (Nat.card ↥(center ↥L))) (hlib : LibData t p f)
    (hX : StatedClassicalModel (↥L ⧸ center ↥L) t 3 p f) :
    ∃ S : Subgroup (↥L ⧸ center ↥L),
      InvData (p ^ f) (↥L ⧸ center ↥L) (QuotientGroup.mk ⟨v, hIL C.v_mem⟩) S := by
  obtain ⟨hinv, -⟩ := hlib _ hX
  have hvL : v ∈ L := hIL C.v_mem
  refine hinv _ ?_ ?_
  · show (QuotientGroup.mk (⟨v, hvL⟩ * ⟨v, hvL⟩) : ↥L ⧸ center ↥L) = 1
    rw [show (⟨v, hvL⟩ * ⟨v, hvL⟩ : ↥L) = 1 from Subtype.ext C.v_sq]
    rfl
  · intro h
    have hz : (⟨v, hvL⟩ : ↥L) ∈ center ↥L := (QuotientGroup.eq_one_iff _).1 h
    exact C.v_ne_one (congrArg Subtype.val (eq_one_of_involution_mem_odd (C := center ↥L) hodd hz
      (Subtype.ext C.v_sq)))

theorem v1_inner_of_lib {t : StatedLieTag} {p f : ℕ} (hlib : LibData t p f) {v w : G}
    {Iv Iw Ivw P : Subgroup G} (C : Conf2A G t p f v w Iv Iw Ivw P) {v₁ : G} (hv₁R : v₁ ∈ P ⊓ Ivw)
    (hv₁2 : v₁ * v₁ = 1) (hv₁1 : v₁ ≠ 1) (hv₁v : v₁ ≠ v) :
    ∃ m ∈ Iw, v₁ * m⁻¹ ∈ centralizer (Iw : Set G) := by
  classical
  by_contra hnot
  have hv2 := C.v_sq
  have hw2 := C.w_sq
  have hv1 := C.v_ne_one
  have hw1 := C.w_ne_one
  have hvIw : v ∈ Iw := C.le_w C.v_mem
  have hvIvw : v ∈ Ivw := C.le_vw C.v_mem
  have hwv : v * w = w * v := C.comm
  have hv₁P : v₁ ∈ P := hv₁R.1
  have hv₁w : v₁ * w = w * v₁ := mem_centralizer_singleton_iff.1 (C.sylow_w.le hv₁P)
  have hvv₁ : v * v₁ = v₁ * v := (C.v_central v₁ hv₁P).symm
  have hv₁N : v₁ ∈ normalizer (Iw : Set G) := C.comp_w.le_normalizer (C.sylow_w.le hv₁P)
  have hIwq : IsQuasisimple ↥Iw := C.comp_w.1.isQuasisimple
  have : Group.IsPerfect ↥Iw := hIwq.1
  have hX : StatedClassicalModel (↥Iw ⧸ center ↥Iw) t 3 p f := by
    rcases C.tag with rfl | rfl
    · exact stated_of_lieModel_PSL C.model_w
    · exact stated_of_lieModel_PSU C.model_w
  obtain ⟨-, hgraph⟩ := hlib _ hX
  obtain ⟨S, hS⟩ := C.exists_S C.le_w C.odd_w hlib hX
  set vb : ↥Iw ⧸ center ↥Iw := QuotientGroup.mk ⟨v, hvIw⟩ with hvb
  set c : MulAut (↥Iw ⧸ center ↥Iw) := normalizerAct Iw ⟨v₁, hv₁N⟩ with hc
  have hc2 : c * c = 1 := by
    rw [hc, ← map_mul]
    have : (⟨v₁, hv₁N⟩ : normalizer (Iw : Set G)) * ⟨v₁, hv₁N⟩ = 1 := Subtype.ext hv₁2
    rw [this, map_one]
  have hcout : c ∉ (inner (↥Iw ⧸ center ↥Iw) : Subgroup (MulAut (↥Iw ⧸ center ↥Iw))) := by
    rintro ⟨y, hy⟩
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective y
    apply hnot
    refine ⟨(m : G), m.2, ?_⟩
    have h1 : normalizerAct Iw ⟨v₁, hv₁N⟩ = normalizerAct Iw ⟨(m : G), Subgroup.le_normalizer m.2⟩ := by
      rw [normalizerAct_of_mem Iw m.2]
      exact hy.symm
    have h2 : normalizerAct Iw (⟨v₁, hv₁N⟩ * ⟨(m : G), Subgroup.le_normalizer m.2⟩⁻¹) = 1 := by
      rw [map_mul, map_inv, h1, mul_inv_cancel]
    have hcc := mem_centralizer_of_normalizerAct_eq_one Iw h2
    simpa using hcc
  have hcvb : c vb = vb := by
    rw [hc, hvb, normalizerAct_apply_mk]
    congr 1
    apply Subtype.ext
    rw [coe_conjOn]
    show v₁ * v * v₁⁻¹ = v
    calc v₁ * v * v₁⁻¹ = (v * v₁) * v₁⁻¹ := by rw [← hvv₁]
      _ = v := by group
  obtain ⟨N, hN⟩ := hgraph c hc2 hcout
  obtain ⟨J₁, hJ₁le, hJ₁q, hJ₁norm⟩ := KGroups.Bal.exists_lift_component C.odd_w hv₁2 hv₁N hN.quasisimple hN.fixed
    hN.conj_mem
  obtain ⟨g, hgI, hg1, hg2⟩ := b_L3_fourgroup G t p f C.tag C.prime.1 C.prime.2.1 C.prime.2.2 Ivw
    C.comp_vw.1.isQuasisimple C.odd_vw C.model_vw v v₁ hvIvw hv₁R.2 hv2 hv₁2 hvv₁ hv1 hv₁1 hv₁v.symm
  have hgc : g * (v * w) = (v * w) * g := mem_centralizer_singleton_iff.1 (C.comp_vw.1.1 hgI)
  have hv₁inv : v₁⁻¹ = v₁ := inv_eq_of_mul_eq_one_right hv₁2
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  have hgw : g * w * g⁻¹ = w * v₁ := by
    have hw_eq : w = (v * w) * v := by
      calc w = (v * v) * w := by rw [hv2, one_mul]
        _ = v * (v * w) := by rw [mul_assoc]
        _ = v * (w * v) := by rw [hwv]
        _ = (v * w) * v := by rw [mul_assoc]
    calc g * w * g⁻¹ = g * ((v * w) * v) * g⁻¹ := by rw [← hw_eq]
      _ = (g * (v * w) * g⁻¹) * (g * v * g⁻¹) := by group
      _ = (v * w) * (v * v₁) := by
          rw [hg1]
          congr 1
          calc g * (v * w) * g⁻¹ = ((v * w) * g) * g⁻¹ := by rw [hgc]
            _ = v * w := by group
      _ = w * v₁ := by
          calc (v * w) * (v * v₁) = v * (w * v) * v₁ := by simp only [mul_assoc]
            _ = v * (v * w) * v₁ := by rw [hwv]
            _ = (v * v) * w * v₁ := by simp only [mul_assoc]
            _ = w * v₁ := by rw [hv2, one_mul]
  have hgiv : g⁻¹ * v * g = v₁ := by
    calc g⁻¹ * v * g = g⁻¹ * (g * v₁ * g⁻¹) * g := by rw [hg2]
      _ = v₁ := by group
  have hgiv₁ : g⁻¹ * v₁ * g = v₁ * v := by
    have e : v = v₁ * (g⁻¹ * v₁ * g) := by
      calc v = g⁻¹ * (g * v * g⁻¹) * g := by group
        _ = g⁻¹ * (v * v₁) * g := by rw [hg1]
        _ = (g⁻¹ * v * g) * (g⁻¹ * v₁ * g) := by group
        _ = v₁ * (g⁻¹ * v₁ * g) := by rw [hgiv]
    calc g⁻¹ * v₁ * g = v₁⁻¹ * (v₁ * (g⁻¹ * v₁ * g)) := by group
      _ = v₁⁻¹ * v := by rw [← e]
      _ = v₁ * v := by rw [hv₁inv]
  have hgiw : g⁻¹ * w * g = w * v * v₁ := by
    have e : w = (g⁻¹ * w * g) * (v₁ * v) := by
      calc w = g⁻¹ * (g * w * g⁻¹) * g := by group
        _ = g⁻¹ * (w * v₁) * g := by rw [hgw]
        _ = (g⁻¹ * w * g) * (g⁻¹ * v₁ * g) := by group
        _ = (g⁻¹ * w * g) * (v₁ * v) := by rw [hgiv₁]
    have hinvvv : (v₁ * v)⁻¹ = v * v₁ := by
      rw [mul_inv_rev, hv₁inv, hvinv]
    calc g⁻¹ * w * g = (g⁻¹ * w * g) * (v₁ * v) * (v₁ * v)⁻¹ := by group
      _ = w * (v₁ * v)⁻¹ := by rw [← e]
      _ = w * v * v₁ := by rw [hinvvv, mul_assoc]
  have hmapconj : ∀ (H : Subgroup G) (x : G),
      x ∈ H.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ H := by
    intro H x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have : g⁻¹ * ((MulAut.conj g).toMonoidHom y) * g = y := by
        simp [MulAut.conj_apply]; group
      rw [this]
      exact hy
    · intro h
      exact ⟨g⁻¹ * x * g, h, by simp [MulAut.conj_apply]; group⟩
  set A₁ : Subgroup G := Iw ⊓ centralizer ({v₁} : Set G) with hA₁
  set J : Subgroup G := J₁.map (MulAut.conj g).toMonoidHom with hJ
  set M : Subgroup G := A₁.map (MulAut.conj g).toMonoidHom with hM
  have hJq : IsQuasisimple ↥J := LocalCores.isQuasisimple_of_mulEquiv
    (J₁.equivMapOfInjective _ (MulAut.conj g).injective) hJ₁q
  have hJM : J ≤ M := Subgroup.map_mono hJ₁le
  set Cv : Subgroup G := centralizer ({v} : Set G) with hCv
  set w₁ : G := w * v₁ with hw₁
  have hw₁v : w₁ * v = v * w₁ := by
    show w * v₁ * v = v * (w * v₁)
    calc w * v₁ * v = w * (v₁ * v) := by rw [mul_assoc]
      _ = w * (v * v₁) := by rw [hvv₁]
      _ = (w * v) * v₁ := by rw [mul_assoc]
      _ = (v * w) * v₁ := by rw [hwv]
      _ = v * (w * v₁) := by rw [mul_assoc]
  have hw₁2 : w₁ * w₁ = 1 := by
    show (w * v₁) * (w * v₁) = 1
    calc (w * v₁) * (w * v₁) = w * (v₁ * w) * v₁ := by simp only [mul_assoc]
      _ = w * (w * v₁) * v₁ := by rw [hv₁w]
      _ = (w * w) * (v₁ * v₁) := by simp only [mul_assoc]
      _ = 1 := by rw [hw2, hv₁2, one_mul]
  have hw₁C : w₁ ∈ Cv := mem_centralizer_singleton_iff.2 hw₁v
  have hcc : ∀ a b : G, a * b = b * a →
      (g * a * g⁻¹) * (g * b * g⁻¹) = (g * b * g⁻¹) * (g * a * g⁻¹) := by
    intro a b h
    calc g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
      _ = g * (b * a) * g⁻¹ := by rw [h]
      _ = g * b * g⁻¹ * (g * a * g⁻¹) := by group
  have hxeq : ∀ x : G, x = g * (g⁻¹ * x * g) * g⁻¹ := fun x => by group
  have hw₁g : w₁ = g * w * g⁻¹ := hgw.symm
  have hvg : v = g * v₁ * g⁻¹ := hg2.symm
  have hMC : M ≤ Cv ⊓ centralizer ({w₁} : Set G) := by
    rintro x hx
    have hx' := (hmapconj A₁ x).1 hx
    obtain ⟨haIw, hav₁⟩ := hx'
    have hav : (g⁻¹ * x * g) * v₁ = v₁ * (g⁻¹ * x * g) := mem_centralizer_singleton_iff.1 hav₁
    have haw : (g⁻¹ * x * g) * w = w * (g⁻¹ * x * g) :=
      mem_centralizer_singleton_iff.1 (C.comp_w.1.1 haIw)
    refine ⟨mem_centralizer_singleton_iff.2 ?_, mem_centralizer_singleton_iff.2 ?_⟩
    · have := hcc _ _ hav
      rw [← hxeq x, ← hvg] at this
      exact this
    · have := hcc _ _ haw
      rw [← hxeq x, ← hw₁g] at this
      exact this
  have hJnorm : ∀ x ∈ M, ∀ y ∈ J, x * y * x⁻¹ ∈ J := by
    intro x hx y hy
    have hx' := (hmapconj A₁ x).1 hx
    have hy' := (hmapconj J₁ y).1 hy
    rw [hmapconj]
    have := hJ₁norm _ hx' _ hy'
    convert this using 1
    group
  have hMnorm : ∀ x ∈ Cv ⊓ centralizer ({w₁} : Set G), ∀ y ∈ M, x * y * x⁻¹ ∈ M := by
    intro x hx y hy
    have hxv : x * v = v * x := mem_centralizer_singleton_iff.1 hx.1
    have hxw : x * w₁ = w₁ * x := mem_centralizer_singleton_iff.1 hx.2
    have hy' := (hmapconj A₁ y).1 hy
    have hcc' : ∀ a b : G, a * b = b * a →
        (g⁻¹ * a * g) * (g⁻¹ * b * g) = (g⁻¹ * b * g) * (g⁻¹ * a * g) := by
      intro a b h
      calc g⁻¹ * a * g * (g⁻¹ * b * g) = g⁻¹ * (a * b) * g := by group
        _ = g⁻¹ * (b * a) * g := by rw [h]
        _ = g⁻¹ * b * g * (g⁻¹ * a * g) := by group
    have hx'v : (g⁻¹ * x * g) * v₁ = v₁ * (g⁻¹ * x * g) := by
      have h1 := hcc' x v hxv
      rwa [hgiv] at h1
    have hgiw₁ : g⁻¹ * w₁ * g = w := by rw [hw₁g]; group
    have hx'w : (g⁻¹ * x * g) * w = w * (g⁻¹ * x * g) := by
      have h1 := hcc' x w₁ hxw
      rwa [hgiw₁] at h1
    have hx'C : g⁻¹ * x * g ∈ centralizer ({w} : Set G) := mem_centralizer_singleton_iff.2 hx'w
    obtain ⟨hbIw, hbv₁⟩ := hy'
    have hb : (g⁻¹ * y * g) * v₁ = v₁ * (g⁻¹ * y * g) := mem_centralizer_singleton_iff.1 hbv₁
    have hmem : (g⁻¹ * x * g) * (g⁻¹ * y * g) * (g⁻¹ * x * g)⁻¹ ∈ A₁ := by
      refine ⟨C.comp_w.conj _ hx'C _ hbIw, mem_centralizer_singleton_iff.2 ?_⟩
      have c1 : Commute (g⁻¹ * x * g) v₁ := hx'v
      have c2 : Commute (g⁻¹ * y * g) v₁ := hb
      exact ((c1.mul_left c2).mul_left c1.inv_left).eq
    rw [hmapconj]
    convert hmem using 1
    group
  have hv₁Iv : ∀ i ∈ Iv, v₁ * i * v₁⁻¹ ∈ Iv := by
    have hX' : StatedClassicalModel (↥Ivw ⧸ center ↥Ivw) t 3 p f := by
      rcases C.tag with rfl | rfl
      · exact stated_of_lieModel_PSL C.model_vw
      · exact stated_of_lieModel_PSU C.model_vw
    obtain ⟨S', hS'⟩ := C.exists_S C.le_vw C.odd_vw hlib hX'
    have himg := C.image_Iv C.le_vw C.odd_vw hS'
    have hv₁Ivw : v₁ ∈ Ivw := hv₁R.2
    have hB : Iv.map (MulAut.conj v₁).toMonoidHom ≤ Iv := by
      refine KGroups.Bal.perfect_le_of_central_coset (A := Iv) (H := Ivw)
        (Z := (center ↥Ivw).map Ivw.subtype) ?_ C.le_vw ?_ ?_ ?_
      · rw [← Subgroup.map_commutator, commutator_self_of_quasisimple C.comp_v.isQuasisimple]
      · rintro _ ⟨z, -, rfl⟩
        exact z.2
      · rintro _ ⟨z, hz, rfl⟩ h hh
        have := Subgroup.mem_center_iff.1 hz ⟨h, hh⟩
        exact (congrArg Subtype.val this).symm
      · rintro _ ⟨i, hi, rfl⟩
        have hiIvw : i ∈ Ivw := C.le_vw hi
        set bb : G := (MulAut.conj v₁).toMonoidHom i with hbb
        have hbbeq : bb = v₁ * i * v₁⁻¹ := by simp [hbb, MulAut.conj_apply]
        have hbbIvw : bb ∈ Ivw := by
          rw [hbbeq]
          exact mul_mem (mul_mem hv₁Ivw hiIvw) (inv_mem hv₁Ivw)
        have hs : QuotientGroup.mk (⟨i, hiIvw⟩ : ↥Ivw) ∈ S' := (himg _).2 ⟨⟨i, hiIvw⟩, hi, rfl⟩
        have hcent : (QuotientGroup.mk (⟨v₁, hv₁Ivw⟩ : ↥Ivw) : ↥Ivw ⧸ center ↥Ivw) ∈
            Subgroup.centralizer ({(QuotientGroup.mk ⟨v, hvIvw⟩ : ↥Ivw ⧸ center ↥Ivw)} :
              Set (↥Ivw ⧸ center ↥Ivw)) := by
          rw [Subgroup.mem_centralizer_singleton_iff]
          show (QuotientGroup.mk (⟨v₁, hv₁Ivw⟩ * ⟨v, hvIvw⟩) : ↥Ivw ⧸ center ↥Ivw) =
            QuotientGroup.mk (⟨v, hvIvw⟩ * ⟨v₁, hv₁Ivw⟩)
          congr 1
          exact Subtype.ext hvv₁.symm
        have hs' := hS'.conj_mem _ hcent _ hs
        have hsb : (QuotientGroup.mk (⟨v₁, hv₁Ivw⟩ : ↥Ivw) : ↥Ivw ⧸ center ↥Ivw) *
            QuotientGroup.mk ⟨i, hiIvw⟩ * (QuotientGroup.mk ⟨v₁, hv₁Ivw⟩)⁻¹ =
            QuotientGroup.mk ⟨bb, hbbIvw⟩ := by
          rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
          congr 1
        rw [hsb] at hs'
        obtain ⟨x, hxIv, hxeq⟩ := (himg _).1 hs'
        refine ⟨(x : G), hxIv, (x : G)⁻¹ * bb, ⟨⟨(x : G)⁻¹ * bb, ?_⟩, ?_, rfl⟩, by group⟩
        · exact mul_mem (inv_mem x.2) hbbIvw
        · have := QuotientGroup.eq.1 hxeq
          exact this
    intro i hi
    exact hB ⟨i, hi, by simp [MulAut.conj_apply]⟩
  have hw₁Iv : ∀ i ∈ Iv, w₁ * i * w₁⁻¹ ∈ Iv := by
    intro i hi
    have hi' := hv₁Iv i hi
    have hwi : w * (v₁ * i * v₁⁻¹) = (v₁ * i * v₁⁻¹) * w :=
      (mem_centralizer_singleton_iff.1 (C.comp_w.1.1 (C.le_w hi'))).symm
    have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
    have : w₁ * i * w₁⁻¹ = v₁ * i * v₁⁻¹ := by
      calc w₁ * i * w₁⁻¹ = w * (v₁ * i * v₁⁻¹) * w⁻¹ := by simp only [hw₁]; group
        _ = (v₁ * i * v₁⁻¹) * w * w⁻¹ := by rw [hwi]
        _ = v₁ * i * v₁⁻¹ := by group
    rw [this]
    exact hi'
  have hsolv : ∀ Q : Subgroup G, Q ≤ Iv →
      (∀ p ∈ Q, w₁ * p * w₁⁻¹ * p⁻¹ ∈ Iv ⊓ centralizer (Iv : Set G)) → Group.IsSolvable ↥Q := by
    intro Q hQI hQ
    have hIvIw : Iv ≤ Iw := C.le_w
    have himgw := C.image_Iv C.le_w C.odd_w hS
    set π : ↥Iw →* ↥Iw ⧸ center ↥Iw := QuotientGroup.mk' (center ↥Iw) with hπ
    set Q' : Subgroup (↥Iw ⧸ center ↥Iw) := (Q.subgroupOf Iw).map π with hQ'
    have hQ'S : Q' ≤ S := by
      rintro _ ⟨x, hx, rfl⟩
      exact (himgw _).2 ⟨x, hQI hx, rfl⟩
    have hQ'cond : ∀ s ∈ Q', c s * s⁻¹ ∈ Subgroup.zpowers vb := by
      rintro _ ⟨x, hx, rfl⟩
      have hxQ : (x : G) ∈ Q := hx
      have hxIv : (x : G) ∈ Iv := hQI hxQ
      have hcomm := hQ (x : G) hxQ
      have hxw : w * (x : G) = (x : G) * w :=
        (mem_centralizer_singleton_iff.1 (C.comp_w.1.1 x.2)).symm
      have hwv₁ : Commute w v₁ := hv₁w.symm
      have heq : w₁ * (x : G) * w₁⁻¹ * (x : G)⁻¹ = v₁ * (x : G) * v₁⁻¹ * (x : G)⁻¹ := by
        have hwy : Commute w (v₁ * (x : G) * v₁⁻¹) :=
          (hwv₁.mul_right (show Commute w (x : G) from hxw)).mul_right hwv₁.inv_right
        calc w₁ * (x : G) * w₁⁻¹ * (x : G)⁻¹ = (w * (v₁ * (x : G) * v₁⁻¹) * w⁻¹) * (x : G)⁻¹ := by
              simp only [hw₁]; group
          _ = v₁ * (x : G) * v₁⁻¹ * (x : G)⁻¹ := by rw [hwy.mul_inv_cancel]
      have hz := C.center_Iv _ hcomm.1 (fun y hy => (mem_centralizer_iff.1 hcomm.2 y hy).symm)
      have hzIw : v₁ * (x : G) * v₁⁻¹ * (x : G)⁻¹ ∈ Iw := by
        rw [← heq]
        exact hIvIw hcomm.1
      have hcx : c (π x) * (π x)⁻¹ = QuotientGroup.mk ⟨v₁ * (x : G) * v₁⁻¹ * (x : G)⁻¹, hzIw⟩ := by
        rw [hc]
        show normalizerAct Iw ⟨v₁, hv₁N⟩ (QuotientGroup.mk x) * (QuotientGroup.mk x)⁻¹ = _
        rw [normalizerAct_apply_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
        congr 1
      rw [hcx]
      rcases hz with h1 | h1
      · have h1' : v₁ * (x : G) * v₁⁻¹ * (x : G)⁻¹ = 1 := heq ▸ h1
        have : (⟨v₁ * (x : G) * v₁⁻¹ * (x : G)⁻¹, hzIw⟩ : ↥Iw) = 1 := Subtype.ext h1'
        rw [this]
        have h1m : (QuotientGroup.mk (1 : ↥Iw) : ↥Iw ⧸ center ↥Iw) = 1 := rfl
        rw [h1m]
        exact one_mem _
      · have h1' : v₁ * (x : G) * v₁⁻¹ * (x : G)⁻¹ = v := heq ▸ h1
        have : (⟨v₁ * (x : G) * v₁⁻¹ * (x : G)⁻¹, hzIw⟩ : ↥Iw) = ⟨v, hvIw⟩ := Subtype.ext h1'
        rw [this]
        exact Subgroup.mem_zpowers vb
    have hsolvQ' := hS.graph_solvable c hc2 hcout hcvb Q' hQ'S hQ'cond
    let φ : ↥Q →* ↥Q' := (π.comp (Subgroup.inclusion (hQI.trans hIvIw))).codRestrict Q'
      (fun x => ⟨Subgroup.inclusion (hQI.trans hIvIw) x, x.2, rfl⟩)
    refine isSolvable_of_central_ker φ ?_ hsolvQ'
    intro x hx
    have h1 : π (Subgroup.inclusion (hQI.trans hIvIw) x) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
    have hcz : Subgroup.inclusion (hQI.trans hIvIw) x ∈ center ↥Iw := (QuotientGroup.eq_one_iff _).1 h1
    rw [Subgroup.mem_center_iff]
    intro y
    have := Subgroup.mem_center_iff.1 hcz (Subgroup.inclusion (hQI.trans hIvIw) y)
    have h' : (y : G) * (x : G) = (x : G) * (y : G) := congrArg Subtype.val this
    exact Subtype.ext h'
  have hMsub := balance_commute_sub hw₁C hw₁2 (I := Iv) (J := J) (M := M) C.comp_v.1 C.comp_v.2 hJq hJM hMC
    hJnorm hMnorm hw₁Iv hsolv
  have hvA₁ : v ∈ A₁ := ⟨hvIw, mem_centralizer_singleton_iff.2 hvv₁⟩
  have hJw : ∀ y ∈ J, w * y * w⁻¹ ∈ J := by
    intro y hy
    have hy₁ := (hmapconj J₁ y).1 hy
    set y₁ := g⁻¹ * y * g with hy₁def
    have hy₁A : y₁ ∈ A₁ := hJ₁le hy₁
    have hwy₁ : Commute w y₁ := (mem_centralizer_singleton_iff.1 (C.comp_w.1.1 hy₁A.1)).symm
    have hv₁y₁ : Commute v₁ y₁ := (mem_centralizer_singleton_iff.1 hy₁A.2).symm
    have hwv' : Commute w v := hwv.symm
    have hwv₁' : Commute w v₁ := hv₁w.symm
    have hu : Commute (w * v₁) y₁ := hwy₁.mul_left hv₁y₁
    have key : g⁻¹ * (w * y * w⁻¹) * g = v * y₁ * v⁻¹ := by
      calc g⁻¹ * (w * y * w⁻¹) * g = (g⁻¹ * w * g) * y₁ * (g⁻¹ * w * g)⁻¹ := by simp only [hy₁def]; group
        _ = (v * (w * v₁)) * y₁ * (v * (w * v₁))⁻¹ := by
            rw [hgiw]
            have : w * v * v₁ = v * (w * v₁) := by
              calc w * v * v₁ = (v * w) * v₁ := by rw [hwv]
                _ = v * (w * v₁) := by rw [mul_assoc]
            rw [this]
        _ = v * ((w * v₁) * y₁ * (w * v₁)⁻¹) * v⁻¹ := by group
        _ = v * y₁ * v⁻¹ := by rw [hu.mul_inv_cancel]
    rw [hJ]
    refine (hmapconj J₁ _).2 ?_
    rw [key]
    exact hJ₁norm v hvA₁ y₁ hy₁
  have hJeven : Even (Nat.card J) := by
    obtain ⟨P', hP'2, hP'4⟩ := exists_two_subgroup_card_ge_four hJq
    obtain ⟨k, hk⟩ := hP'2.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [hk] at hP'4
      omega
    have h2 : 2 ∣ Nat.card P' := by
      rw [hk]
      exact dvd_pow_self 2 hk0
    exact even_iff_two_dvd.2 (h2.trans (Subgroup.card_subgroup_dvd_card P'))
  obtain ⟨j, hjJ, hj2, hj1, hjw⟩ := KGroups.Bal.exists_fixed_involution hw2 hJw hJeven
  have hjv : j * v = v * j := mem_centralizer_singleton_iff.1 (hMC (hJM hjJ)).1
  have hjIv : ∀ x ∈ Iv, x * j = j * x := fun x hx => mem_centralizer_iff.1 (hMsub hjJ) x hx
  have hjCw : j ∈ centralizer ({w} : Set G) := mem_centralizer_singleton_iff.2 hjw.symm
  have hjN : j ∈ normalizer (Iw : Set G) := C.comp_w.le_normalizer hjCw
  have hQ := sylow_inf_centralizer C.sylow_w C.comp_w.le_normalizer
  have hrk : NoCommInv (centralizer ({w} : Set G) ⊓ centralizer (Iw : Set G)) :=
    noCommInv_of_sylow hQ (noCommInv_of_cyclic C.Q_cyc)
  have hwC : w ∈ centralizer ({w} : Set G) ⊓ centralizer (Iw : Set G) := by
    refine ⟨mem_centralizer_singleton_iff.2 rfl, ?_⟩
    exact mem_centralizer_iff.2 fun h hh => mem_centralizer_singleton_iff.1 (C.comp_w.1.1 hh)
  have hσ2 : normalizerAct Iw ⟨j, hjN⟩ * normalizerAct Iw ⟨j, hjN⟩ = 1 := by
    rw [← map_mul]
    have : (⟨j, hjN⟩ : normalizer (Iw : Set G)) * ⟨j, hjN⟩ = 1 := Subtype.ext hj2
    rw [this, map_one]
  have hσfix : ∀ s ∈ S, normalizerAct Iw ⟨j, hjN⟩ s = s := by
    intro s hs
    obtain ⟨x, hxIv, rfl⟩ := (C.image_Iv C.le_w C.odd_w hS s).1 hs
    rw [normalizerAct_apply_mk]
    congr 1
    apply Subtype.ext
    rw [coe_conjOn]
    show j * (x : G) * j⁻¹ = x
    have := hjIv (x : G) hxIv
    calc j * (x : G) * j⁻¹ = (x * j) * j⁻¹ := by rw [this]
      _ = x := by group
  have hjcases : j = w ∨ j = v ∨ j = w * v := by
    rcases hS.aut_fixing _ hσ2 hσfix with h | h
    · left
      have hjC : j ∈ centralizer ({w} : Set G) ⊓ centralizer (Iw : Set G) :=
        ⟨hjCw, mem_centralizer_of_normalizerAct_eq_one Iw h⟩
      rcases hrk j hjC w hwC hj2 hw2 hjw.symm with h1 | h1 | h1
      · exact absurd h1 hj1
      · exact absurd h1 hw1
      · exact h1
    · right
      have h1 : normalizerAct Iw (⟨j, hjN⟩ * ⟨v, Subgroup.le_normalizer hvIw⟩⁻¹) = 1 := by
        rw [map_mul, map_inv, h, normalizerAct_of_mem Iw hvIw, mul_inv_cancel]
      have hjv' : j * v ∈ centralizer (Iw : Set G) := by
        have := mem_centralizer_of_normalizerAct_eq_one Iw h1
        simpa [hvinv] using this
      have hjvw : Commute (j * v) w :=
        (show Commute j w from hjw.symm).mul_left (show Commute v w from hwv)
      have hjvC : j * v ∈ centralizer ({w} : Set G) ⊓ centralizer (Iw : Set G) :=
        ⟨mem_centralizer_singleton_iff.2 hjvw.eq, hjv'⟩
      have hjv2 : (j * v) * (j * v) = 1 := by
        calc j * v * (j * v) = j * (v * j) * v := by simp only [mul_assoc]
          _ = j * (j * v) * v := by rw [← hjv]
          _ = (j * j) * (v * v) := by simp only [mul_assoc]
          _ = 1 := by rw [hj2, hv2, one_mul]
      rcases hrk (j * v) hjvC w hwC hjv2 hw2 hjvw.eq with h1 | h1 | h1
      · left
        calc j = (j * v) * v⁻¹ := by group
          _ = v := by rw [h1, one_mul, hvinv]
      · exact absurd h1 hw1
      · right
        calc j = (j * v) * v⁻¹ := by group
          _ = w * v := by rw [h1, hvinv]
  have hJ₁Iw : ∀ y ∈ J₁, y ∈ Iw := fun y hy => (hJ₁le hy).1
  rcases hjcases with hjw' | hjv' | hjwv'
  ·
    rw [hjw'] at hjJ
    have h1 := (hmapconj J₁ w).1 hjJ
    rw [hgiw] at h1
    have h2 : w * v * v₁ * v ∈ Iw := mul_mem (hJ₁Iw _ h1) hvIw
    have h3 : w * v * v₁ * v = w * v₁ := by
      calc w * v * v₁ * v = w * v * (v₁ * v) := by rw [mul_assoc (w * v)]
        _ = w * v * (v * v₁) := by rw [← hvv₁]
        _ = w * (v * v) * v₁ := by simp only [mul_assoc]
        _ = w * v₁ := by rw [hv2, mul_one]
    rw [h3] at h2
    exact v1_not_wI C hv₁R hv₁2 hv₁1 hv₁v h2
  ·
    rw [hjv'] at hjJ
    have h1 := (hmapconj J₁ v).1 hjJ
    rw [hgiv] at h1
    exact hnot ⟨v₁, hJ₁Iw _ h1, by rw [mul_inv_cancel]; exact one_mem _⟩
  ·
    rw [hjwv'] at hjJ
    have h1 := (hmapconj J₁ (w * v)).1 hjJ
    have h2 : g⁻¹ * (w * v) * g = w * v := by
      calc g⁻¹ * (w * v) * g = (g⁻¹ * w * g) * (g⁻¹ * v * g) := by group
        _ = (w * v * v₁) * v₁ := by rw [hgiw, hgiv]
        _ = w * v := by rw [mul_assoc, hv₁2, mul_one]
    rw [h2] at h1
    have hwIw : w ∈ Iw := by
      have h3 : w * v * v ∈ Iw := mul_mem (hJ₁Iw _ h1) hvIw
      rwa [mul_assoc, hv2, mul_one] at h3
    have hz : (⟨w, hwIw⟩ : ↥Iw) ∈ center ↥Iw := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (mem_centralizer_singleton_iff.1 (C.comp_w.1.1 y.2))
    exact hw1 (congrArg Subtype.val (eq_one_of_involution_mem_odd (C := center ↥Iw) C.odd_w hz
      (Subtype.ext hw2)))

end Main


@[expose] def B_S3_v1_inner_neg_uni : Prop :=
  ∀ (G : Type) [Group G] [Finite G], GlobalHyp G →
    ∀ (p f : ℕ) (v w : G) (Iv Iw Ivw P : Subgroup G),
      Conf2A G .PSU p f v w Iv Iw Ivw P → p ^ f % 4 = 1 →
      ∀ v₁ : G, v₁ ∈ P ⊓ Ivw → v₁ * v₁ = 1 → v₁ ≠ 1 → v₁ ≠ v →
        ((∃ u ∈ P ⊓ Ivw, u * u = 1 ∧ u ≠ 1 ∧ u ≠ v ∧ ∃ s ∈ P ⊓ Ivw, s * s = u) →
          ∃ s ∈ P ⊓ Ivw, s * s = v₁) →
        ∃ m ∈ Iw, v₁ * m⁻¹ ∈ centralizer (Iw : Set G)

theorem b_S3_v1_inner_neg_of_uni (h : B_S3_v1_inner_neg_uni) : B_S3_v1_inner_neg := by
  intro G _ _ hG t p f v w Iv Iw Ivw P hconf hcong v₁ hv₁R hv₁2 hv₁1 hv₁v hsq
  rcases hconf.tag with rfl | rfl
  · exact v1_inner_of_lib (libData_lin hconf.prime.1 hconf.prime.2.1 hconf.prime.2.2 (hcong.1 rfl)) hconf
      hv₁R hv₁2 hv₁1 hv₁v
  · exact h G hG p f v w Iv Iw Ivw P hconf (hcong.2 rfl) v₁ hv₁R hv₁2 hv₁1 hv₁v hsq

end CFSG.GH74.Generic.S3
