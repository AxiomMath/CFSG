module

public import CFSG.CGT.Foote82.Lemma61
public import CFSG.LargeExtraspecial.S5Comp
public import CFSG.GH74.Uniqueness.SU.SU10Fusion
public import CFSG.LocalAnalysis.ZStar
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Quasithin.Background.G11Basic
public import CFSG.CGT.Foote82.T66.MC1Steps

public section

namespace CFSG.CGT.Foote82.BAS

open CFSG.Open CFSG.Quasithin.G11

section Conj

variable {Γ : Type*} [Group Γ]

abbrev conjSg (g : Γ) (H : Subgroup Γ) : Subgroup Γ := H.map (MulAut.conj g).toMonoidHom

theorem mem_conjSg {g x : Γ} {H : Subgroup Γ} : x ∈ conjSg g H ↔ g⁻¹ * x * g ∈ H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro hx
    exact ⟨g⁻¹ * x * g, hx, by simp [mul_assoc]⟩

theorem conj_mem_conjSg {g y : Γ} {H : Subgroup Γ} (hy : y ∈ H) : g * y * g⁻¹ ∈ conjSg g H :=
  ⟨y, hy, rfl⟩

theorem conjSg_mul (g h : Γ) (H : Subgroup Γ) : conjSg (g * h) H = conjSg g (conjSg h H) := by
  ext x
  simp only [mem_conjSg, mul_inv_rev]
  constructor <;> intro hx <;> simpa [mul_assoc] using hx

theorem conjSg_one (H : Subgroup Γ) : conjSg 1 H = H := by
  ext x
  simp [mem_conjSg]

theorem conjSg_conjSg_inv (g : Γ) (H : Subgroup Γ) : conjSg g (conjSg g⁻¹ H) = H := by
  rw [← conjSg_mul, mul_inv_cancel, conjSg_one]

theorem conjSg_mono {g : Γ} {H K : Subgroup Γ} (h : H ≤ K) : conjSg g H ≤ conjSg g K :=
  Subgroup.map_mono h

theorem conjSg_of_mem {g : Γ} {H : Subgroup Γ} (hg : g ∈ H) : conjSg g H = H := by
  ext x
  rw [mem_conjSg]
  constructor
  · intro hx
    simpa [mul_assoc] using H.mul_mem (H.mul_mem hg hx) (H.inv_mem hg)
  · intro hx
    exact H.mul_mem (H.mul_mem (H.inv_mem hg) hx) hg

theorem conjSg_inf (g : Γ) (H K : Subgroup Γ) : conjSg g (H ⊓ K) = conjSg g H ⊓ conjSg g K := by
  ext x
  simp only [mem_conjSg, Subgroup.mem_inf]

theorem conjSg_commutator (g : Γ) (H K : Subgroup Γ) :
    conjSg g ⁅H, K⁆ = ⁅conjSg g H, conjSg g K⁆ :=
  Subgroup.map_commutator _ _ _

theorem conjSg_eq_bot_iff {g : Γ} {H : Subgroup Γ} : conjSg g H = ⊥ ↔ H = ⊥ :=
  Subgroup.map_eq_bot_iff_of_injective H (MulAut.conj g).injective

theorem mem_centralizer_conjSg {g x : Γ} {H : Subgroup Γ} :
    x ∈ Subgroup.centralizer (conjSg g H : Set Γ) ↔
      g⁻¹ * x * g ∈ Subgroup.centralizer (H : Set Γ) := by
  simp only [Subgroup.mem_centralizer_iff]
  constructor
  · intro hx y hy
    have := hx (g * y * g⁻¹) (conj_mem_conjSg hy)
    have h2 : g⁻¹ * (g * y * g⁻¹ * x) * g = g⁻¹ * (x * (g * y * g⁻¹)) * g := by rw [this]
    simpa [mul_assoc] using h2
  · intro hx y hy
    have hy' : g⁻¹ * y * g ∈ H := mem_conjSg.1 hy
    have := hx _ hy'
    have h2 : g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ =
        g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by rw [this]
    simpa [mul_assoc] using h2

theorem conjSg_centralizer_singleton (g t : Γ) :
    conjSg g (Subgroup.centralizer ({t} : Set Γ)) =
      Subgroup.centralizer ({g * t * g⁻¹} : Set Γ) := by
  ext x
  rw [mem_conjSg]
  simp only [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc x * (g * t * g⁻¹) = g * ((g⁻¹ * x * g) * t) * g⁻¹ := by group
      _ = g * (t * (g⁻¹ * x * g)) * g⁻¹ := by rw [h]
      _ = g * t * g⁻¹ * x := by group
  · intro h
    calc g⁻¹ * x * g * t = g⁻¹ * (x * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * x) * g := by rw [h]
      _ = t * (g⁻¹ * x * g) := by group

theorem mem_normalizer_conjSg {g x : Γ} {H : Subgroup Γ} :
    x ∈ Subgroup.normalizer (conjSg g H : Set Γ) ↔
      g⁻¹ * x * g ∈ Subgroup.normalizer (H : Set Γ) := by
  simp only [Subgroup.mem_normalizer_iff, SetLike.mem_coe, mem_conjSg]
  constructor
  · intro hx y
    have := hx (g * y * g⁻¹)
    simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] at this
    simpa [mul_assoc] using this
  · intro hx y
    have := hx (g⁻¹ * y * g)
    simpa [mul_assoc] using this

theorem conjSg_normalizer (g : Γ) (H : Subgroup Γ) :
    conjSg g (Subgroup.normalizer (H : Set Γ)) =
      Subgroup.normalizer (conjSg g H : Set Γ) := by
  ext x
  rw [mem_conjSg, mem_normalizer_conjSg]

theorem mem_normalizer_iff_conjSg_eq {x : Γ} {H : Subgroup Γ} [Finite H] :
    x ∈ Subgroup.normalizer (H : Set Γ) ↔ conjSg x H = H := by
  constructor
  · intro hx
    refine le_antisymm ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.1 hx y).1 hy
    · intro y hy
      rw [mem_conjSg]
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hx) y).1 hy
      simpa using this
  · intro hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [← hx]
      exact conj_mem_conjSg hy
    · intro hy
      rw [← hx, mem_conjSg] at hy
      simpa [mul_assoc] using hy

theorem isComponentOf_conjSg {H K : Subgroup Γ} (g : Γ) (h : IsComponentOf H K) :
    IsComponentOf (conjSg g H) (conjSg g K) :=
  ⟨Subgroup.map_mono h.1, h.2.1.map _,
    Open.IsQuasisimple.of_mulEquiv
      (H.equivMapOfInjective _ (MulAut.conj g).injective).symm h.2.2⟩

theorem commutator_sup_zpowers_le (N : Subgroup Γ) [N.Normal]
    (t : Γ) : ⁅N ⊔ Subgroup.zpowers t, N ⊔ Subgroup.zpowers t⁆ ≤ N := by
  have hmap : (N ⊔ Subgroup.zpowers t).map (QuotientGroup.mk' N) =
      Subgroup.zpowers (QuotientGroup.mk' N t) := by
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq, MonoidHom.map_zpowers]
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have ha' : QuotientGroup.mk' N a ∈ Subgroup.zpowers (QuotientGroup.mk' N t) :=
    hmap ▸ Subgroup.mem_map_of_mem _ ha
  have hb' : QuotientGroup.mk' N b ∈ Subgroup.zpowers (QuotientGroup.mk' N t) :=
    hmap ▸ Subgroup.mem_map_of_mem _ hb
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 ha'
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hb'
  rw [← QuotientGroup.eq_one_iff (N := N), ← QuotientGroup.mk'_apply,
    map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, ← hi, ← hj]
  exact (Commute.zpow_zpow_self _ i j).eq

theorem orderOf_conj (k x : Γ) : orderOf (k * x * k⁻¹) = orderOf x := by
  have : k * x * k⁻¹ = MulAut.conj k x := rfl
  rw [this, MulEquiv.orderOf_eq]

end Conj

section CommSpace

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem glv_mul_apply (a b : GLV V) (v : V) : (a * b) v = a (b v) := rfl

theorem glv_inv_apply_apply (a : GLV V) (v : V) : a⁻¹ (a v) = v := a.symm_apply_apply v

theorem glv_apply_inv_apply (a : GLV V) (v : V) : a (a⁻¹ v) = v := a.apply_symm_apply v

theorem commSpace_conjSg (g : GLV V) (K : Subgroup (GLV V)) (U : Submodule (ZMod 2) V) :
    commSpace (conjSg g K) (conjSub g U) = conjSub g (commSpace K U) := by
  unfold commSpace conjSub
  rw [Submodule.map_span]
  congr 1
  ext w
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨k', ⟨k, hk, rfl⟩, u', ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨k u - u, ⟨k, hk, u, hu, rfl⟩, ?_⟩
    show g (k u - u) = (g * k * g⁻¹) (g u) - g u
    rw [map_sub, glv_mul_apply, glv_mul_apply, glv_inv_apply_apply]
  · rintro ⟨_, ⟨k, hk, u, hu, rfl⟩, rfl⟩
    refine ⟨g * k * g⁻¹, ⟨k, hk, rfl⟩, g u, ⟨u, hu, rfl⟩, ?_⟩
    show g (k u - u) = (g * k * g⁻¹) (g u) - g u
    rw [map_sub, glv_mul_apply, glv_mul_apply, glv_inv_apply_apply]

theorem conjSg_zpowers (g x : GLV V) :
    conjSg g (Subgroup.zpowers x) = Subgroup.zpowers (g * x * g⁻¹) :=
  MonoidHom.map_zpowers _ x

theorem commSpace_zpowers_conj (g x : GLV V) :
    commSpace (Subgroup.zpowers (g * x * g⁻¹)) ⊤ =
      conjSub g (commSpace (Subgroup.zpowers x) ⊤) := by
  rw [← conjSg_zpowers, ← commSpace_conjSg, conjSub_top]

theorem mem_commSpace_zpowers_conj {g x : GLV V} {v : V} :
    v ∈ commSpace (Subgroup.zpowers (g * x * g⁻¹)) ⊤ ↔
      g⁻¹ v ∈ commSpace (Subgroup.zpowers x) ⊤ := by
  rw [commSpace_zpowers_conj, mem_conjSub]
  rfl

theorem mem_vFix_conj {g x : GLV V} {v : V} :
    x ∈ vFix v ↔ g⁻¹ * x * g ∈ vFix (g⁻¹ v) := by
  show x v = v ↔ (g⁻¹ * x * g) (g⁻¹ v) = g⁻¹ v
  rw [glv_mul_apply, glv_mul_apply, glv_apply_inv_apply]
  constructor
  · intro h
    rw [h]
  · intro h
    have := congrArg g h
    rwa [glv_apply_inv_apply, glv_apply_inv_apply] at this

end CommSpace

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {G L : Subgroup (GLV V)} {z : GLV V}

private theorem eq_bot_of_le_center {A B : Subgroup (GLV V)} (hperf : ⁅A, A⁆ = A)
    (hc' : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hAB : A ≤ B) : A = ⊥ := by
  have h : ⁅A, A⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (hc' b hb a (hAB ha))
  rwa [hperf] at h

structure Hyp (G L : Subgroup (GLV V)) (z : GLV V) : Prop where
  conf : OddTranspConf G L z

namespace Hyp

variable (hc : Hyp G L z)
include hc

theorem setup : Setup6Irr G (Subgroup.zpowers z) L := hc.conf.std.extremal.setup

theorem z_mem : z ∈ G := hc.setup.S_le (Subgroup.mem_zpowers z)

theorem orderOf_z : orderOf z = 2 := hc.conf.std.orderOf_s

theorem z_mul_z : z * z = 1 := by
  have h := pow_orderOf_eq_one z
  rw [hc.orderOf_z, sq] at h
  exact h

theorem L_le : L ≤ G := hc.conf.std.extremal.toConf66.L_le

theorem quasisimple : Open.IsQuasisimple ↥L := hc.setup.component.2.2

theorem perfect : ⁅L, L⁆ = L := by
  have : Group.IsPerfect ↥L := ⟨hc.quasisimple.1⟩
  exact Subgroup.isPerfect_iff.mp this

theorem L_ne_bot : L ≠ ⊥ := by
  intro h
  have hq := hc.quasisimple
  have : Nontrivial (↥L ⧸ Subgroup.center ↥L) := hq.2.toNontrivial
  obtain ⟨a, b, hab⟩ := exists_pair_ne (↥L ⧸ Subgroup.center ↥L)
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  have ha : a = 1 := Subtype.ext (by simpa [h] using a.2)
  have hb : b = 1 := Subtype.ext (by simpa [h] using b.2)
  rw [ha, hb]

theorem faithful : FaithfulTildeV L := hc.conf.std.extremal.faithful

theorem irrTilde : HasIrrTildeV L := hc.setup.irrTilde

theorem irr : IsIrr G ⊤ := hc.setup.irr

theorem centralizer_zpowers : Subgroup.centralizer ((Subgroup.zpowers z : Subgroup (GLV V)) :
    Set (GLV V)) = Subgroup.centralizer ({z} : Set (GLV V)) := by
  ext x
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact (h z (Subgroup.mem_zpowers z)).symm
  · intro h y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact ((Commute.zpow_left h.symm n)).eq

theorem component : IsComponentOf L (G ⊓ Subgroup.centralizer ({z} : Set (GLV V))) := by
  have h := hc.setup.component
  rwa [hc.centralizer_zpowers] at h

theorem z_mem_centralizer : z ∈ Subgroup.centralizer (L : Set (GLV V)) := by
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have h2 : l ∈ Subgroup.centralizer ({z} : Set (GLV V)) := (hc.component.1 hl).2
  rw [Subgroup.mem_centralizer_singleton_iff] at h2
  exact h2

theorem z_mem_K : z ∈ G ⊓ Subgroup.centralizer (L : Set (GLV V)) :=
  ⟨hc.z_mem, hc.z_mem_centralizer⟩

theorem z_ne_one : z ≠ 1 := by
  intro h
  have := hc.orderOf_z
  rw [h, orderOf_one] at this
  exact absurd this (by norm_num)

theorem conjSg_G {g : GLV V} (hg : g ∈ G) : conjSg g G = G := conjSg_of_mem hg

theorem conjSg_L_le {g : GLV V} (hg : g ∈ G) : conjSg g L ≤ G := by
  rw [← hc.conjSg_G hg]
  exact conjSg_mono hc.L_le

theorem conj_z_mem {g : GLV V} (hg : g ∈ G) : g * z * g⁻¹ ∈ G :=
  G.mul_mem (G.mul_mem hg hc.z_mem) (G.inv_mem hg)

theorem orderOf_conj_z (g : GLV V) : orderOf (g * z * g⁻¹) = 2 := by
  rw [orderOf_conj, hc.orderOf_z]

theorem component_conj {g : GLV V} (hg : g ∈ G) :
    IsComponentOf (conjSg g L) (G ⊓ Subgroup.centralizer ({g * z * g⁻¹} : Set (GLV V))) := by
  have h := isComponentOf_conjSg g hc.component
  rwa [conjSg_inf, hc.conjSg_G hg, conjSg_centralizer_singleton] at h

theorem conj_z_mem_centralizer (g : GLV V) :
    g * z * g⁻¹ ∈ Subgroup.centralizer (conjSg g L : Set (GLV V)) := by
  rw [mem_centralizer_conjSg]
  simpa [mul_assoc] using hc.z_mem_centralizer

theorem commutator_conj_ne_bot {a b : GLV V} (ha : a ∈ G) (hb : b ∈ G) :
    ⁅conjSg a L, conjSg b L⁆ ≠ ⊥ := by
  have h := hc.conf.std.commutator_ne_bot (a⁻¹ * b) (G.mul_mem (G.inv_mem ha) hb)
  intro h0
  apply h
  have : conjSg a ⁅L, conjSg (a⁻¹ * b) L⁆ = ⊥ := by
    rw [conjSg_commutator, ← conjSg_mul, mul_inv_cancel_left]
    exact h0
  rwa [conjSg_eq_bot_iff] at this

theorem eq_of_isComponentOf {a b : GLV V} (ha : a ∈ G) (hb : b ∈ G) {H : Subgroup (GLV V)}
    (hA : IsComponentOf (conjSg a L) H) (hB : IsComponentOf (conjSg b L) H) :
    conjSg a L = conjSg b L := by
  by_contra hne
  exact hc.commutator_conj_ne_bot ha hb
    (CFSG.LargeExtraspecial.S5.commute_of_isComponentOf_ne hA hB hne)

theorem component_of_inv_conj {g t : GLV V} (hg : g ∈ G) (htG : t ∈ G) (ht : orderOf t = 2)
    (htc : t ∈ Subgroup.centralizer (conjSg g L : Set (GLV V))) :
    IsComponentOf (conjSg g L) (G ⊓ Subgroup.centralizer ({t} : Set (GLV V))) := by
  have h1 : g⁻¹ * t * g ∈ G := G.mul_mem (G.mul_mem (G.inv_mem hg) htG) hg
  have h2 : orderOf (g⁻¹ * t * g) = 2 := by
    have := orderOf_conj g⁻¹ t
    rwa [inv_inv, ht] at this
  have h3 : g⁻¹ * t * g ∈ Subgroup.centralizer (L : Set (GLV V)) :=
    mem_centralizer_conjSg.1 htc
  have h := isComponentOf_conjSg g (hc.conf.std.component_of_inv _ h1 h2 h3)
  rwa [conjSg_inf, hc.conjSg_G hg, conjSg_centralizer_singleton,
    show g * (g⁻¹ * t * g) * g⁻¹ = t by group] at h

theorem normalizer_of_centralizer {g t : GLV V} (hg : g ∈ G) (htG : t ∈ G) (ht : orderOf t = 2)
    (htc : t ∈ Subgroup.centralizer (conjSg g L : Set (GLV V))) :
    G ⊓ Subgroup.centralizer ({t} : Set (GLV V)) ≤ Subgroup.normalizer (conjSg g L : Set (GLV V)) := by
  intro x hx
  have hcomp := hc.component_of_inv_conj hg htG ht htc
  have hcomp' := CFSG.LargeExtraspecial.S5.isComponentOf_map_conj hcomp hx
  have hxg : x * g ∈ G := G.mul_mem hx.1 hg
  have heq : conjSg (x * g) L = conjSg g L := by
    refine hc.eq_of_isComponentOf hxg hg ?_ hcomp
    rwa [conjSg_mul]
  rw [mem_normalizer_iff_conjSg_eq, ← conjSg_mul]
  exact heq

theorem centralizer_conj_z_le {g : GLV V} (hg : g ∈ G) :
    G ⊓ Subgroup.centralizer ({g * z * g⁻¹} : Set (GLV V)) ≤
      Subgroup.normalizer (conjSg g L : Set (GLV V)) :=
  hc.normalizer_of_centralizer hg (hc.conj_z_mem hg) (hc.orderOf_conj_z g)
    (hc.conj_z_mem_centralizer g)

theorem centralizer_z_le : G ⊓ Subgroup.centralizer ({z} : Set (GLV V)) ≤
    Subgroup.normalizer (L : Set (GLV V)) := by
  have h := hc.centralizer_conj_z_le G.one_mem
  simpa [conjSg_one] using h

theorem quasisimple_conj (g : GLV V) : Open.IsQuasisimple ↥(conjSg g L) :=
  Open.IsQuasisimple.of_mulEquiv (L.equivMapOfInjective _ (MulAut.conj g).injective).symm
    hc.quasisimple

theorem perfect_conj (g : GLV V) : ⁅conjSg g L, conjSg g L⁆ = conjSg g L := by
  rw [← conjSg_commutator, hc.perfect]

theorem conj_ne_bot (g : GLV V) : conjSg g L ≠ ⊥ := by
  rw [Ne, conjSg_eq_bot_iff]
  exact hc.L_ne_bot

theorem eq_of_normalizes {a b : GLV V} (ha : a ∈ G) (hb : b ∈ G)
    (hab : conjSg a L ≤ Subgroup.normalizer (conjSg b L : Set (GLV V)))
    (hba : conjSg b L ≤ Subgroup.normalizer (conjSg a L : Set (GLV V))) :
    conjSg a L = conjSg b L := by
  set A := conjSg a L with hA
  set B := conjSg b L with hB
  have hnorm : ∀ x ∈ A, ∀ n ∈ A ⊓ B, x * n * x⁻¹ ∈ A ⊓ B := by
    intro x hx n hn
    refine ⟨A.mul_mem (A.mul_mem hx hn.1) (A.inv_mem hx), ?_⟩
    exact (Subgroup.mem_normalizer_iff.1 (hab hx) n).1 hn.2
  rcases CFSG.LargeExtraspecial.S5.commute_or_eq_of_normalized (hc.quasisimple_conj a)
      inf_le_left hnorm with hcent | heq
  ·
    exfalso
    have hcomm : ⁅A, B⁆ ≤ A ⊓ B := by
      rw [Subgroup.commutator_le]
      intro x hx y hy
      refine ⟨?_, ?_⟩
      · have h1 : y * x⁻¹ * y⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 (hba hy) x⁻¹).1
          (A.inv_mem hx)
        have : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
        rw [commutatorElement_def, this]
        exact A.mul_mem hx h1
      · have h1 : x * y * x⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.1 (hab hx) y).1 hy
        rw [commutatorElement_def]
        exact B.mul_mem h1 (B.inv_mem hy)
    have h1 : ⁅⁅A, B⁆, A⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (hcent x (hcomm hx) y hy).symm
    have h2 : ⁅⁅B, A⁆, A⁆ = ⊥ := by
      rw [Subgroup.commutator_comm B A]
      exact h1
    have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
    rw [hc.perfect_conj a] at h3
    exact hc.commutator_conj_ne_bot ha hb h3
  ·
    have hAB : A ≤ B := fun x hx => by
      have hx' : x ∈ conjSg a L ⊓ B := heq.symm ▸ hx
      exact hx'.2
    have hnorm' : ∀ x ∈ B, ∀ n ∈ A, x * n * x⁻¹ ∈ A := fun x hx n hn =>
      (Subgroup.mem_normalizer_iff.1 (hba hx) n).1 hn
    rcases CFSG.LargeExtraspecial.S5.commute_or_eq_of_normalized (hc.quasisimple_conj b)
        hAB hnorm' with hcent | heq'
    · exact absurd (eq_bot_of_le_center (hc.perfect_conj a) hcent hAB) (hc.conj_ne_bot a)
    · exact heq'

theorem eq_z_of_commute {u : GLV V} (hu : u ∈ G ⊓ Subgroup.centralizer (L : Set (GLV V)))
    (hu2 : orderOf u = 2) (huz : u * z = z * u) : u = z := by
  by_contra hne
  have := CFSG.GH74.Uniqueness.SU.SU10.two_le_pRank_of_commuting_involutions hu hc.z_mem_K hu2
    hc.orderOf_z hne huz
  rw [hc.conf.rank] at this
  omega

theorem eq_conj_z_of_commute {g u : GLV V} (hg : g ∈ G) (huG : u ∈ G)
    (hu : u ∈ Subgroup.centralizer (conjSg g L : Set (GLV V))) (hu2 : orderOf u = 2)
    (huz : u * (g * z * g⁻¹) = (g * z * g⁻¹) * u) : u = g * z * g⁻¹ := by
  have h1 : g⁻¹ * u * g ∈ G ⊓ Subgroup.centralizer (L : Set (GLV V)) :=
    ⟨G.mul_mem (G.mul_mem (G.inv_mem hg) huG) hg, mem_centralizer_conjSg.1 hu⟩
  have h2 : orderOf (g⁻¹ * u * g) = 2 := by
    have := orderOf_conj g⁻¹ u
    rwa [inv_inv, hu2] at this
  have h3 : (g⁻¹ * u * g) * z = z * (g⁻¹ * u * g) := by
    calc (g⁻¹ * u * g) * z = g⁻¹ * (u * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * u) * g := by rw [huz]
      _ = z * (g⁻¹ * u * g) := by group
  have := hc.eq_z_of_commute h1 h2 h3
  calc u = g * (g⁻¹ * u * g) * g⁻¹ := by group
    _ = g * z * g⁻¹ := by rw [this]

theorem fix_commSpace_z : ∀ l ∈ L, ∀ w ∈ commSpace (Subgroup.zpowers z) ⊤, l w = w :=
  (hc.setup.toSetup6.lemma61 (Subgroup.mem_zpowers z)).1

theorem fix_commSpace_conj (g : GLV V) :
    ∀ l ∈ conjSg g L, ∀ w ∈ commSpace (Subgroup.zpowers (g * z * g⁻¹)) ⊤, l w = w := by
  intro l hl w hw
  rw [mem_conjSg] at hl
  rw [mem_commSpace_zpowers_conj] at hw
  have := hc.fix_commSpace_z _ hl _ hw
  rw [glv_mul_apply, glv_mul_apply, glv_apply_inv_apply] at this
  have h2 := congrArg g this
  rwa [glv_apply_inv_apply, glv_apply_inv_apply] at h2

theorem branchA_conj {g : GLV V} (hg : g ∈ G) {v : V}
    (hv : v ∈ commSpace (Subgroup.zpowers (g * z * g⁻¹)) ⊤) (hv0 : v ≠ 0) :
    G ⊓ vFix v ≤ Subgroup.normalizer (conjSg g L : Set (GLV V)) := by
  intro x hx
  rw [mem_commSpace_zpowers_conj] at hv
  have hv0' : g⁻¹ v ≠ 0 := by
    intro h
    apply hv0
    have := congrArg g h
    rwa [glv_apply_inv_apply, map_zero] at this
  have hx' : g⁻¹ * x * g ∈ G ⊓ vFix (g⁻¹ v) :=
    ⟨G.mul_mem (G.mul_mem (G.inv_mem hg) hx.1) hg, mem_vFix_conj.1 hx.2⟩
  have := hc.conf.branchA _ hv hv0' hx'
  rw [mem_normalizer_conjSg]
  exact this

theorem eq_of_commSpace_inf {a b : GLV V} (ha : a ∈ G) (hb : b ∈ G)
    (hab : commSpace (Subgroup.zpowers (a * z * a⁻¹)) ⊤ ⊓
      commSpace (Subgroup.zpowers (b * z * b⁻¹)) ⊤ ≠ ⊥) :
    conjSg a L = conjSg b L := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hab
  have hLa : conjSg a L ≤ G ⊓ vFix x := fun l hl =>
    ⟨hc.conjSg_L_le ha hl, hc.fix_commSpace_conj a l hl x hx.1⟩
  have hLb : conjSg b L ≤ G ⊓ vFix x := fun l hl =>
    ⟨hc.conjSg_L_le hb hl, hc.fix_commSpace_conj b l hl x hx.2⟩
  exact hc.eq_of_normalizes ha hb (hLa.trans (hc.branchA_conj hb hx.2 hx0))
    (hLb.trans (hc.branchA_conj ha hx.1 hx0))

theorem mem_normalizer_of_Dz {g : GLV V} (hg : g ∈ G) (hne : g * z * g⁻¹ ≠ z)
    (hcomm : (g * z * g⁻¹) * z = z * (g * z * g⁻¹)) :
    g * z * g⁻¹ ∈ Subgroup.normalizer (L : Set (GLV V)) ∧
      g * z * g⁻¹ ∉ Subgroup.centralizer (L : Set (GLV V)) := by
  refine ⟨hc.centralizer_z_le ⟨hc.conj_z_mem hg,
    Subgroup.mem_centralizer_singleton_iff.2 hcomm⟩, fun hd => ?_⟩
  · exact hne (hc.eq_z_of_commute ⟨hc.conj_z_mem hg, hd⟩ (hc.orderOf_conj_z g) hcomm)

theorem exists_Dz : ∃ g ∈ G, g * z * g⁻¹ ≠ z ∧ (g * z * g⁻¹) * z = z * (g * z * g⁻¹) := by
  by_contra hcon
  push Not at hcon
  letI : Fintype ↥G := Fintype.ofFinite _
  set t : ↥G := ⟨z, hc.z_mem⟩ with ht
  have ht1 : t ≠ 1 := fun h => hc.z_ne_one (congrArg Subtype.val h)
  have ht2 : t * t = 1 := Subtype.ext hc.z_mul_z
  have hiso : ∀ g : ↥G, (g * t * g⁻¹) * t = t * (g * t * g⁻¹) → g * t * g⁻¹ = t := by
    intro g hg
    by_contra hne
    exact hcon g g.2 (fun h => hne (Subtype.ext h)) (congrArg Subtype.val hg)
  obtain ⟨N, hN, hodd, hNt⟩ := CFSG.ZStar.glauberman_zStar ↥G t ht1 ht2 hiso
  have hgen : (⊤ : Subgroup ↥G) ≤ N ⊔ Subgroup.zpowers t := by
    have hle : G ≤ (N ⊔ Subgroup.zpowers t).map G.subtype := by
      conv_lhs => rw [hc.conf.gen]
      rw [Subgroup.closure_le]
      rintro _ ⟨g, hg, rfl⟩
      refine ⟨⟨g, hg⟩ * t * ⟨g, hg⟩⁻¹, ?_, rfl⟩
      have h1 : (⟨g, hg⟩ : ↥G) * t * ⟨g, hg⟩⁻¹ =
          ((⟨g, hg⟩ : ↥G) * t * ⟨g, hg⟩⁻¹ * t⁻¹) * t := by group
      rw [h1]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hNt _))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
    intro y _
    obtain ⟨y', hy', hyy⟩ := hle y.2
    have : y' = y := Subtype.ext hyy
    exact this ▸ hy'
  have hperf' : ⁅L.subgroupOf G, L.subgroupOf G⁆ = L.subgroupOf G := by
    apply Subgroup.map_injective G.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hc.L_le]
    exact hc.perfect
  have hL : L.subgroupOf G ≤ N := by
    rw [← hperf']
    exact (Subgroup.commutator_mono (le_top.trans hgen) (le_top.trans hgen)).trans
      (commutator_sup_zpowers_le N t)
  have hsolv : Group.IsSolvable ↥N := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hLsolv : Group.IsSolvable ↥L :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.inclusion hL).comp (Subgroup.subgroupOfEquivOfLe hc.L_le).symm.toMonoidHom)
      ((Subgroup.inclusion_injective hL).comp (Subgroup.subgroupOfEquivOfLe hc.L_le).symm.injective)
  have : Nontrivial ↥L := (Subgroup.nontrivial_iff_ne_bot L).mpr hc.L_ne_bot
  have : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hc.perfect
  exact Group.IsPerfect.not_isSolvable ↥L hLsolv

end Hyp

end CFSG.CGT.Foote82.BAS
