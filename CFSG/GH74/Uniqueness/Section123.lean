module

public import CFSG.GH74.Uniqueness.Section12Transport
public import CFSG.GH74.Uniqueness.Section12BenderSub
public import CFSG.GH74.Uniqueness.Bender.Embedding

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

section Center

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem A2.eq_one_of_forall_commute
    (S : ZDSetup X Z M) {v : X} (hv : ∀ g : X, g * v = v * g) :
    v = 1 := by
  have : IsSimpleGroup X := S.theorem1_unconditional.1
  have hc : center X = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top (center X) with h | h
    · exact h
    · exfalso
      apply S.cor714_not_comm
      intro a b
      have hb : b ∈ center X := h ▸ mem_top b
      exact mem_center_iff.mp hb a
  have hvc : v ∈ center X := mem_center_iff.mpr hv
  rw [hc, mem_bot] at hvc
  exact hvc

theorem A2.centralizer_ne_top
    (S : ZDSetup X Z M) {v : X} (hv : v ≠ 1) :
    centralizer ({v} : Set X) ≠ ⊤ := by
  intro htop
  apply hv
  refine A2.eq_one_of_forall_commute S fun g => ?_
  have hg : g ∈ centralizer ({v} : Set X) := htop ▸ mem_top g
  exact mem_centralizer_singleton_iff.mp hg

end Center

section Odd

theorem A2.eq_of_inv_mul_mem_of_odd {G : Type} [Group G] {N : Subgroup G}
    (hN : Odd (Nat.card N)) (hNc : N ≤ center G) {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a⁻¹ * b ∈ N) : a = b := by
  have hbo : b = a * (a⁻¹ * b) := by rw [mul_inv_cancel_left]
  have hoa : a * (a⁻¹ * b) = (a⁻¹ * b) * a := mem_center_iff.mp (hNc hab) a
  have hoo : (a⁻¹ * b) * (a⁻¹ * b) = 1 := by
    have h1 : b * b = (a * a) * ((a⁻¹ * b) * (a⁻¹ * b)) := by
      calc b * b = (a * (a⁻¹ * b)) * (a * (a⁻¹ * b)) := by rw [← hbo]
        _ = a * ((a⁻¹ * b) * a) * (a⁻¹ * b) := by group
        _ = a * (a * (a⁻¹ * b)) * (a⁻¹ * b) := by rw [hoa]
        _ = (a * a) * ((a⁻¹ * b) * (a⁻¹ * b)) := by group
    rw [hb, ha, one_mul] at h1
    exact h1.symm
  have h1 := eq_one_of_mem_of_sq_eq_one hN hab hoo
  rw [hbo, h1, mul_one]

end Odd

section BenderSubAPI

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem A2.center_le_of_benderSub (S : ZDSetup X Z M) {F : Subgroup X} {n i e : ℕ}
    (hB : BenderSub Z M F n i e) : center ↥F ≤ (M ⊓ F).subgroupOf F := by
  obtain ⟨z₀, hz₀, hz₀FM⟩ := hB.nonempty
  obtain ⟨hz₀F, hz₀M⟩ := mem_inf.mp hz₀FM
  intro x hx
  have hxz : (⟨z₀, hz₀F⟩ : ↥F) * x = x * ⟨z₀, hz₀F⟩ := mem_center_iff.mp hx _
  have hxM : (x : X) ∈ M := S.prodDisc.centralizer_le_of_mem hz₀ hz₀M
    (mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hxz).symm)
  exact mem_subgroupOf.mpr (mem_inf.mpr ⟨hxM, x.2⟩)

theorem A2.odd_card_center_of_benderSub {F : Subgroup X} {n i e : ℕ}
    (hB : BenderSub Z M F n i e) : Odd (Nat.card (center ↥F)) := by
  have h1 := odd_card_pPrimeCoreIn F
  rwa [hB.core, card_map_of_injective F.subtype_injective] at h1

theorem A2.mk_mem_normalizer_iff (S : ZDSetup X Z M) {F : Subgroup X} {n i e : ℕ}
    (hB : BenderSub Z M F n i e) {T : Sylow 2 (↥F ⧸ center ↥F)}
    (hT : ((M ⊓ F).subgroupOf F).map (QuotientGroup.mk' (center ↥F)) =
      normalizer ((T : Subgroup (↥F ⧸ center ↥F)) : Set (↥F ⧸ center ↥F))) (g : ↥F) :
    QuotientGroup.mk' (center ↥F) g ∈
        normalizer ((T : Subgroup (↥F ⧸ center ↥F)) : Set (↥F ⧸ center ↥F)) ↔ (g : X) ∈ M := by
  rw [← hT]
  constructor
  · rintro ⟨y, hy, hyg⟩
    have h1 : y⁻¹ * g ∈ center ↥F := QuotientGroup.eq.mp hyg
    have h2 : y * (y⁻¹ * g) ∈ (M ⊓ F).subgroupOf F :=
      ((M ⊓ F).subgroupOf F).mul_mem hy (A2.center_le_of_benderSub S hB h1)
    rw [mul_inv_cancel_left] at h2
    exact (mem_inf.mp (mem_subgroupOf.mp h2)).1
  · intro hg
    exact mem_map_of_mem _ (mem_subgroupOf.mpr (mem_inf.mpr ⟨hg, g.2⟩))

theorem A2.ncard_inter_of_benderSub
    (S : ZDSetup X Z M) {F : Subgroup X} {n i e : ℕ}
    (hB : BenderSub Z M F n i e) :
    (Z ∩ ((F ⊓ M : Subgroup X) : Set X)).ncard = 2 ^ n - 1 := by
  obtain ⟨T, hT⟩ := hB.borel
  obtain ⟨t, hc⟩ := hB.bender.exists_benderCore T
  have hY : ∀ g : ↥F, QuotientGroup.mk' (center ↥F) g ∈
      normalizer ((T : Subgroup (↥F ⧸ center ↥F)) : Set (↥F ⧸ center ↥F)) ↔
        g ∈ (M ⊓ F).subgroupOf F := by
    intro g
    rw [A2.mk_mem_normalizer_iff S hB hT g, mem_subgroupOf, mem_inf]
    exact ⟨fun h => ⟨h, g.2⟩, fun h => h.1⟩
  have hcount := Cor713.ncard_involutions_eq (QuotientGroup.mk' (center ↥F))
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) (A2.odd_card_center_of_benderSub hB)
    (fun o ho g => (mem_center_iff.mp ho g).symm) hY
  have e1 : {k : ↥F ⧸ center ↥F | k ∈ normalizer ((T : Subgroup (↥F ⧸ center ↥F)) :
      Set (↥F ⧸ center ↥F)) ∧ orderOf k = 2} =
      ((Bender.rootCenter (T : Subgroup (↥F ⧸ center ↥F)) : Subgroup (↥F ⧸ center ↥F)) :
        Set (↥F ⧸ center ↥F)) \ {1} := by
    ext g
    exact hc.involution_iff
  have h2 : ((Bender.rootCenter (T : Subgroup (↥F ⧸ center ↥F)) : Subgroup (↥F ⧸ center ↥F)) :
      Set (↥F ⧸ center ↥F)).ncard = 2 ^ n := by
    rw [← Nat.card_coe_set_eq]
    exact hc.card_center
  rw [e1, Set.ncard_sdiff_singleton_of_mem (Subgroup.one_mem _), h2] at hcount
  have himage : (Subtype.val : ↥F → X) '' {y : ↥F | y ∈ (M ⊓ F).subgroupOf F ∧ orderOf y = 2} =
      Z ∩ ((F ⊓ M : Subgroup X) : Set X) := by
    ext x
    constructor
    · rintro ⟨y, ⟨hyY, hy2⟩, rfl⟩
      have hyMF := mem_subgroupOf.mp hyY
      refine ⟨hB.invol y y.2 (by rw [Subgroup.orderOf_coe]; exact hy2), ?_⟩
      exact mem_inf.mpr ⟨y.2, (mem_inf.mp hyMF).1⟩
    · rintro ⟨hxZ, hxFM⟩
      obtain ⟨hxF, hxM⟩ := mem_inf.mp hxFM
      refine ⟨⟨x, hxF⟩, ⟨mem_subgroupOf.mpr (mem_inf.mpr ⟨hxM, hxF⟩), ?_⟩, rfl⟩
      rw [Subgroup.orderOf_mk]
      exact S.invariant.1 x hxZ
  rw [← himage, Set.ncard_image_of_injective _ Subtype.val_injective, hcount]

theorem A2.exists_conj_of_benderSub
    (S : ZDSetup X Z M) {F : Subgroup X} {n i e : ℕ}
    (hB : BenderSub Z M F n i e) {x y : X} (hx : x ∈ Z ∩ ((F ⊓ M : Subgroup X) : Set X))
    (hy : y ∈ Z ∩ ((F ⊓ M : Subgroup X) : Set X)) : ∃ g ∈ M ⊓ F, g⁻¹ * x * g = y := by
  obtain ⟨T, hT⟩ := hB.borel
  obtain ⟨t, hc⟩ := hB.bender.exists_benderCore T
  have hodd := A2.odd_card_center_of_benderSub hB
  obtain ⟨hxZ, hxFM⟩ := hx
  obtain ⟨hxF, hxM⟩ := mem_inf.mp hxFM
  obtain ⟨hyZ, hyFM⟩ := hy
  obtain ⟨hyF, hyM⟩ := mem_inf.mp hyFM
  have himg : ∀ (w : X) (hwZ : w ∈ Z) (hwF : w ∈ F), w ∈ M →
      QuotientGroup.mk' (center ↥F) ⟨w, hwF⟩ ∈ Bender.rootCenter (T : Subgroup (↥F ⧸ center ↥F)) ∧
        QuotientGroup.mk' (center ↥F) ⟨w, hwF⟩ ≠ 1 := by
    intro w hwZ hwF hwM
    have hw2 : orderOf (⟨w, hwF⟩ : ↥F) = 2 := by
      rw [Subgroup.orderOf_mk]
      exact S.invariant.1 w hwZ
    have hne : QuotientGroup.mk' (center ↥F) ⟨w, hwF⟩ ≠ 1 := by
      intro h1
      have hmem : (⟨w, hwF⟩ : ↥F) ∈ center ↥F := (QuotientGroup.eq_one_iff _).mp h1
      exact CFSG.OddInversion.notMem_of_odd_card hodd hw2 hmem
    apply hc.involution_iff.mp
    refine ⟨(A2.mk_mem_normalizer_iff S hB hT _).mpr hwM, orderOf_eq_prime ?_ hne⟩
    have hww : (⟨w, hwF⟩ : ↥F) * ⟨w, hwF⟩ = 1 := Subtype.ext (S.invariant.mul_self_eq_one hwZ)
    rw [sq, ← map_mul, hww, map_one]
  obtain ⟨hxR, hx1⟩ := himg x hxZ hxF hxM
  obtain ⟨hyR, hy1⟩ := himg y hyZ hyF hyM
  obtain ⟨d, hd, hdd⟩ := hc.exists_cartan_conj hxR hx1 hyR hy1
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (center ↥F) d
  have hgM : (g : X) ∈ M :=
    (A2.mk_mem_normalizer_iff S hB hT g).mp (Bender.cartan_le_borel _ _ hd)
  refine ⟨g, mem_inf.mpr ⟨hgM, g.2⟩, ?_⟩
  have h1 : QuotientGroup.mk' (center ↥F) (g⁻¹ * ⟨x, hxF⟩ * g) =
      QuotientGroup.mk' (center ↥F) ⟨y, hyF⟩ := by
    rw [map_mul, map_mul, map_inv]
    exact hdd.symm
  have hab : (g⁻¹ * ⟨x, hxF⟩ * g)⁻¹ * ⟨y, hyF⟩ ∈ center ↥F := QuotientGroup.eq.mp h1
  have hxx : (⟨x, hxF⟩ : ↥F) * ⟨x, hxF⟩ = 1 := Subtype.ext (S.invariant.mul_self_eq_one hxZ)
  have hyy : (⟨y, hyF⟩ : ↥F) * ⟨y, hyF⟩ = 1 := Subtype.ext (S.invariant.mul_self_eq_one hyZ)
  have hgg : (g⁻¹ * ⟨x, hxF⟩ * g) * (g⁻¹ * ⟨x, hxF⟩ * g) = 1 := by
    calc (g⁻¹ * ⟨x, hxF⟩ * g) * (g⁻¹ * ⟨x, hxF⟩ * g) = g⁻¹ * (⟨x, hxF⟩ * ⟨x, hxF⟩) * g := by
          group
      _ = 1 := by rw [hxx]; group
  have heq := A2.eq_of_inv_mul_mem_of_odd hodd le_rfl hgg hyy hab
  exact congrArg Subtype.val heq

end BenderSubAPI

section Lemma123

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem A2.L_le_cenHull (S : ZDSetup X Z M) (c : Ctx12 Z M) {v : X}
    (hv : v ∈ centralizer (c.L : Set X)) : c.L ≤ cenHull Z v := by
  have hLC : c.L ≤ centralizer ({v} : Set X) := fun y hy =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hv y hy)
  calc c.L = zHull Z c.L := (IsProductDisconnected.zHull_lSubgroup S.invariant c.ht c.hz M).symm
    _ ≤ cenHull Z v := closure_mono fun x hx => ⟨hx.1, hLC hx.2⟩

theorem A2.ncard_zM {c : Ctx12 Z M} {n i : ℕ} (h : LData c n i) :
    (Z ∩ (M : Set X)).ncard = 2 ^ n - 1 := by
  have h1 : Z ∩ (M : Set X) = (zHull Z M : Set X) \ {1} := h.zM_eq
  have h2 : ((zHull Z M : Subgroup X) : Set X).ncard = 2 ^ n := by
    rw [← Nat.card_coe_set_eq]
    exact h.m_card
  rw [h1, Set.ncard_sdiff_singleton_of_mem (Subgroup.one_mem _), h2]

theorem ZDSetup.lemma123
    (S : ZDSetup X Z M) : Lemma123Stmt Z M := by
  intro c n i h v hv hv1
  have hZ := S.invariant
  have hLv : c.L ≤ cenHull Z v := A2.L_le_cenHull S c hv
  by_cases heq : cenHull Z v = c.L
  · exact Or.inl heq
  right
  have hLC : c.L ≤ centralizer ({v} : Set X) := fun y hy =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hv y hy)
  have hF : centralizer ({v} : Set X) ≠ ⊤ := A2.centralizer_ne_top S hv1
  have hFM : ¬ centralizer ({v} : Set X) ≤ M := fun hle => c.htM (hle (hLC c.t_mem_L))
  have hne : (Z ∩ ((centralizer ({v} : Set X) ⊓ M : Subgroup X) : Set X)).Nonempty :=
    ⟨c.z, c.hz, mem_inf.mpr ⟨hLC c.z_mem_L, c.hzM⟩⟩
  have hns : ¬ Group.IsSolvable ↥(zHull Z (centralizer ({v} : Set X))) := by
    intro hsol
    have : IsSimpleGroup ↥c.L := h.bender.isSimple
    have hLsol : Group.IsSolvable ↥c.L :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hLv)
        (Subgroup.inclusion_injective hLv)
    exact h.bender.isSimpleBenderGroup.not_commutative
      ((IsSimpleGroup.comm_iff_isSolvable (G := ↥c.L)).mpr hLsol)
  obtain ⟨n', i', e', hB⟩ := S.benderSub_exists hF hFM hne hns
  have hB : BenderSub Z M (cenHull Z v) n' i' e' := hB
  have hZM : Z ∩ ((cenHull Z v ⊓ M : Subgroup X) : Set X) = Z ∩ (M : Set X) := by
    ext x
    constructor
    · rintro ⟨hxZ, hxLM⟩
      exact ⟨hxZ, (mem_inf.mp hxLM).2⟩
    · rintro ⟨hxZ, hxM⟩
      refine ⟨hxZ, mem_inf.mpr ⟨hLv ?_, hxM⟩⟩
      exact IsProductDisconnected.inter_le_lSubgroup hZ S.prodDisc c.ht c.htM c.hz c.hzM ⟨hxZ, hxM⟩
  have hn : n' = n := by
    have h1 := A2.ncard_inter_of_benderSub S hB
    rw [hZM, A2.ncard_zM h] at h1
    have h2 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have h3 : 1 ≤ 2 ^ n' := Nat.one_le_two_pow
    exact Nat.pow_right_injective le_rfl (by omega : 2 ^ n' = 2 ^ n)
  subst n'
  have hcL : center ↥c.L = ⊥ := h.center_eq_bot
  let ι : ↥c.L →* ↥(cenHull Z v) ⧸ center ↥(cenHull Z v) :=
    (QuotientGroup.mk' (center ↥(cenHull Z v))).comp (Subgroup.inclusion hLv)
  have hιinj : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro l hl
    have hmem : Subgroup.inclusion hLv l ∈ center ↥(cenHull Z v) :=
      (QuotientGroup.eq_one_iff _).mp hl
    have hlc : l ∈ center ↥c.L := by
      rw [mem_center_iff]
      intro g
      apply Subtype.ext
      have h1 := congrArg Subtype.val (mem_center_iff.mp hmem (Subgroup.inclusion hLv g))
      exact h1
    rw [hcL, mem_bot] at hlc
    exact hlc
  rcases Bender.BenderType.embedding_index h.bender hB.bender ι hιinj with hii | ⟨hi1, hi3⟩
  ·
    exfalso
    apply heq
    subst hii
    have he' : e' = 1 := by
      rcases hB.bender.cases' with ⟨-, he, -⟩ | ⟨-, he, -⟩ | ⟨hi3, -, -⟩
      · exact he
      · exact he
      · rcases h.hi with h1 | h1 <;> omega
    subst he'
    have hcard : Nat.card (↥(cenHull Z v) ⧸ center ↥(cenHull Z v)) ≤ Nat.card ↥c.L := by
      rw [h.bender.card_eq, hB.bender.card_eq]
    have hsurj : Function.Surjective ι := (hιinj.bijective_of_nat_card_le hcard).2
    have hodd := A2.odd_card_center_of_benderSub hB
    refine le_antisymm ((closure_le _).mpr ?_) hLv
    rintro s ⟨hsZ, hsC⟩
    have hsF : s ∈ cenHull Z v := subset_closure ⟨hsZ, hsC⟩
    obtain ⟨l, hl⟩ := hsurj (QuotientGroup.mk' (center ↥(cenHull Z v)) ⟨s, hsF⟩)
    have hc : (Subgroup.inclusion hLv l)⁻¹ * ⟨s, hsF⟩ ∈ center ↥(cenHull Z v) :=
      QuotientGroup.eq.mp hl
    have hss : (⟨s, hsF⟩ : ↥(cenHull Z v)) * ⟨s, hsF⟩ = 1 :=
      Subtype.ext (hZ.mul_self_eq_one hsZ)
    have hbo : (⟨s, hsF⟩ : ↥(cenHull Z v)) = Subgroup.inclusion hLv l *
        ((Subgroup.inclusion hLv l)⁻¹ * ⟨s, hsF⟩) := by
      rw [mul_inv_cancel_left]
    have hoa : Subgroup.inclusion hLv l * ((Subgroup.inclusion hLv l)⁻¹ * ⟨s, hsF⟩) =
        ((Subgroup.inclusion hLv l)⁻¹ * ⟨s, hsF⟩) * Subgroup.inclusion hLv l :=
      mem_center_iff.mp hc _
    have h1 : (Subgroup.inclusion hLv l * Subgroup.inclusion hLv l) *
        (((Subgroup.inclusion hLv l)⁻¹ * ⟨s, hsF⟩) * ((Subgroup.inclusion hLv l)⁻¹ * ⟨s, hsF⟩)) =
          1 := by
      rw [← hss]
      conv_rhs => rw [hbo]
      calc (Subgroup.inclusion hLv l * Subgroup.inclusion hLv l) *
            (((Subgroup.inclusion hLv l)⁻¹ * ⟨s, hsF⟩) * ((Subgroup.inclusion hLv l)⁻¹ * ⟨s, hsF⟩))
          = Subgroup.inclusion hLv l * (Subgroup.inclusion hLv l *
              ((Subgroup.inclusion hLv l)⁻¹ * ⟨s, hsF⟩)) *
              ((Subgroup.inclusion hLv l)⁻¹ * ⟨s, hsF⟩) := by group
        _ = Subgroup.inclusion hLv l * (((Subgroup.inclusion hLv l)⁻¹ * ⟨s, hsF⟩) *
              Subgroup.inclusion hLv l) * ((Subgroup.inclusion hLv l)⁻¹ * ⟨s, hsF⟩) := by
            rw [hoa]
        _ = (Subgroup.inclusion hLv l * ((Subgroup.inclusion hLv l)⁻¹ * ⟨s, hsF⟩)) *
              (Subgroup.inclusion hLv l * ((Subgroup.inclusion hLv l)⁻¹ * ⟨s, hsF⟩)) := by group
    have haa : Subgroup.inclusion hLv l * Subgroup.inclusion hLv l ∈ center ↥(cenHull Z v) := by
      rw [eq_inv_of_mul_eq_one_left h1]
      exact (center _).inv_mem ((center _).mul_mem hc hc)
    have hll : l * l = 1 := by
      apply hιinj
      rw [map_mul, map_one]
      change QuotientGroup.mk' (center ↥(cenHull Z v)) (Subgroup.inclusion hLv l) *
        QuotientGroup.mk' (center ↥(cenHull Z v)) (Subgroup.inclusion hLv l) = 1
      rw [← map_mul]
      exact (QuotientGroup.eq_one_iff _).mpr haa
    have haa1 : Subgroup.inclusion hLv l * Subgroup.inclusion hLv l = 1 := by
      rw [← map_mul, hll, map_one]
    rw [haa1, one_mul] at h1
    have ho1 := eq_one_of_mem_of_sq_eq_one hodd hc h1
    have hsl : (⟨s, hsF⟩ : ↥(cenHull Z v)) = Subgroup.inclusion hLv l := by
      rw [hbo, ho1, mul_one]
    have hsl' : s = (l : X) := congrArg Subtype.val hsl
    rw [SetLike.mem_coe, hsl']
    exact l.2
  · exact ⟨hi1, lt_of_le_of_ne hLv (Ne.symm heq), e', hi3 ▸ hB⟩

end Lemma123

end CFSG.GH74.Uniqueness
