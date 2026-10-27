module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_6_Defs
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.SCpLemmas
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.PrimeDegreeAction
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_6_9_1
import CFSG.LocalAnalysis.GLTheoremB.PCompBasics
import CFSG.Quasithin.Background.F918V5GComp
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

theorem i116pI_comm {X : Type*} [Group X] {p : ℕ} {B : Subgroup X} (hB : IsElemAbelian p B)
    {a b : X} (ha : a ∈ B) (hb : b ∈ B) : a * b = b * a := CFSG.Open.IsElemAbelian.comm hB ha hb

theorem i116pI_isComponentOf {X : Type*} [Group X] {p : ℕ}
    (hO : GLAPPrimeCore p X = ⊥) {L : Subgroup X} (hL : GLAPComponent p ⊤ L) :
    IsComponentOf L ⊤ := by
  have hZ : GLAPPrimeCore p (↥(⊤ : Subgroup X)) = ⊥ := by
    have h1 := glaPPrimeCore_map_iso p (Subgroup.topEquiv (G := X))
    rw [hO] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.topEquiv (G := X)).injective).1 h1
  have hinj : Function.Injective (QuotientGroup.mk' (GLAPPrimeCore p (↥(⊤ : Subgroup X)))) := by
    intro a b h
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hZ,
      Subgroup.mem_bot] at h
    exact inv_mul_eq_one.mp h
  let e : (↥(⊤ : Subgroup X)) ≃* (↥(⊤ : Subgroup X) ⧸ GLAPPrimeCore p (↥(⊤ : Subgroup X))) :=
    MulEquiv.ofBijective (QuotientGroup.mk' _) ⟨hinj, QuotientGroup.mk'_surjective _⟩
  have h2 : IsComponentOf (L.subgroupOf ⊤) ⊤ :=
    (CFSG.ComponentClassification.LocalComponents.equiv_iff e (L.subgroupOf ⊤)).1 hL.2.2.1
  have h3 := (CFSG.ComponentClassification.LocalComponents.equiv_iff
    (Subgroup.topEquiv (G := X)) (L.subgroupOf ⊤)).2 h2
  have h4 : (L.subgroupOf (⊤ : Subgroup X)).map (Subgroup.topEquiv (G := X)).toMonoidHom = L := by
    ext x
    simp [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  rwa [h4] at h3

def i116pI_J {X : Type*} [Group X] (B L : Subgroup X) : Subgroup X :=
  ⨆ g ∈ B, GLBConj g L

def i116pI_Conj {X : Type*} [Group X] (B L M : Subgroup X) : Prop :=
  ∃ g ∈ B, M = GLBConj g L

section Basic

variable {X : Type*} [Group X] {B L : Subgroup X}

theorem i116pI_le_J {g : X} (hg : g ∈ B) : GLBConj g L ≤ i116pI_J B L :=
  le_iSup₂_of_le g hg le_rfl

theorem i116pI_gLBConj_eq_of_le {g : X} {H : Subgroup X} (h1 : GLBConj g H ≤ H)
    (h2 : GLBConj g⁻¹ H ≤ H) : GLBConj g H = H := by
  refine le_antisymm h1 ?_
  have := gLBConj_mono g h2
  rwa [gLBConj_gLBConj_inv] at this

theorem i116pI_gLBConj_J_le {g : X} (hg : g ∈ B) :
    GLBConj g (i116pI_J B L) ≤ i116pI_J B L := by
  unfold i116pI_J GLBConj
  rw [Subgroup.map_iSup]
  refine iSup_le fun g' => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hg' => ?_
  have := i116pI_le_J (L := L) (B.mul_mem hg' hg)
  rwa [← gLBConj_gLBConj] at this

theorem i116pI_mem_normalizer_J {g : X} (hg : g ∈ B) :
    g ∈ Subgroup.normalizer (i116pI_J B L : Set X) := by
  rw [mem_normalizer_iff_gLBConj_eq]
  exact i116pI_gLBConj_eq_of_le (i116pI_gLBConj_J_le hg) (i116pI_gLBConj_J_le (B.inv_mem hg))

theorem i116pI_isComponentOf_conj (hL : IsComponentOf L ⊤) {M : Subgroup X}
    (hM : i116pI_Conj B L M) : IsComponentOf M ⊤ := by
  obtain ⟨g, _, rfl⟩ := hM
  exact isComponentOf_gLBConj hL g

theorem i116pI_mem_normalizer_of_commute {J : Subgroup X} {e : X}
    (h : ∀ j ∈ J, e * j = j * e) : e ∈ Subgroup.normalizer (J : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro j
  constructor
  · intro hj
    have : e * j * e⁻¹ = j := by rw [h j hj]; group
    rw [this]; exact hj
  · intro hj
    have h1 := h _ hj
    have h2 : e * j * e⁻¹ = j := by
      have : e * (e * j * e⁻¹) = e * j := by rw [h1]; group
      exact mul_left_cancel this
    rwa [h2] at hj

theorem i116pI_centralizes_J [Finite X] (hL : IsComponentOf L ⊤) {E : Subgroup X}
    (hE : IsComponentOf E ⊤) (h : ¬ i116pI_Conj B L E) {e : X} (he : e ∈ E) {j : X}
    (hj : j ∈ i116pI_J B L) : e * j = j * e := by
  have hle : i116pI_J B L ≤ Subgroup.centralizer ({e} : Set X) := by
    refine iSup₂_le fun g hg m hm => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    rcases CFSG.Quasithin.F918V5G.isComponentOf_eq_or_commute hE
      (i116pI_isComponentOf_conj hL ⟨g, hg, rfl⟩) with h1 | h1
    · exact absurd ⟨g, hg, h1⟩ h
    · exact (h1 e he m hm).symm
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hj)).symm

theorem i116pI_comp_le_normalizer_J [Finite X] (hL : IsComponentOf L ⊤) {E : Subgroup X}
    (hE : IsComponentOf E ⊤) : E ≤ Subgroup.normalizer (i116pI_J B L : Set X) := by
  by_cases h : i116pI_Conj B L E
  · obtain ⟨g, hg, rfl⟩ := h
    exact (i116pI_le_J hg).trans Subgroup.le_normalizer
  · intro e he
    exact i116pI_mem_normalizer_of_commute fun j hj => i116pI_centralizes_J hL hE h he hj

theorem i116pI_conj_mem_normalizer_J [Finite X] (hL : IsComponentOf L ⊤) {x : X}
    (hx : x ∈ i116pI_J B L) (y : X) : y * x * y⁻¹ ∈ Subgroup.normalizer (i116pI_J B L : Set X) := by
  have hle : i116pI_J B L ≤ GLBConj y (Subgroup.normalizer (i116pI_J B L : Set X)) := by
    refine iSup₂_le fun g hg x' hx' => ?_
    rw [mem_gLBConj]
    refine i116pI_comp_le_normalizer_J hL (E := GLBConj (g * y⁻¹) L) ?_ ?_
    · exact isComponentOf_gLBConj hL _
    · rw [← gLBConj_gLBConj, mem_gLBConj, inv_inv,
        show y⁻¹ * (y * x' * y⁻¹) * y = x' by group]
      exact hx'
  exact mem_gLBConj.1 (hle hx)

theorem i116pI_conj_mem_J [Finite X] {p : ℕ} (hL : IsComponentOf L ⊤) {Y : Subgroup X}
    (hYc : Nat.Coprime p (Nat.card Y)) (hBY : B ≤ Subgroup.normalizer (Y : Set X)) {x : X}
    (hxB : x ∈ B) (hxJ : x ∈ i116pI_J B L) (hxp : x ^ p = 1) {y : X} (hy : y ∈ Y) :
    y * x * y⁻¹ ∈ i116pI_J B L := by
  set J := i116pI_J B L with hJ
  set N := Subgroup.normalizer (J : Set X) with hN
  have hJN : J ≤ N := Subgroup.le_normalizer
  have hnorm : (J.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJN).2 le_rfl
  set z : X := y * x * y⁻¹ with hz
  have hzN : z ∈ N := i116pI_conj_mem_normalizer_J hL hxJ y
  have hxN : x ∈ N := hJN hxJ
  set u : X := x⁻¹ * z with hu
  have huN : u ∈ N := N.mul_mem (N.inv_mem hxN) hzN
  have huY : u ∈ Y := by
    have h1 := (Subgroup.mem_normalizer_iff.1 (hBY (B.inv_mem hxB)) y).1 hy
    have : u = (x⁻¹ * y * x⁻¹⁻¹) * y⁻¹ := by
      rw [hu, hz]; group
    rw [this]
    exact Y.mul_mem h1 (Y.inv_mem hy)
  have hzp : z ^ p = 1 := by
    rw [hz, conj_pow, hxp]; simp
  let π := QuotientGroup.mk' (J.subgroupOf N)
  let zN : ↥N := ⟨z, hzN⟩
  let uN : ↥N := ⟨u, huN⟩
  let xN : ↥N := ⟨x, hxN⟩
  have hπx : π xN = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact (Subgroup.mem_subgroupOf).2 hxJ
  have hzu : zN = xN * uN := by
    apply Subtype.ext
    simp [zN, xN, uN, hu]
  have hπz : π zN = π uN := by
    rw [hzu, map_mul, hπx, one_mul]
  have h1 : (π uN) ^ p = 1 := by
    rw [← hπz, ← map_pow]
    have : zN ^ p = 1 := Subtype.ext (by simpa [zN] using hzp)
    rw [this, map_one]
  have h2 : (π uN) ^ Nat.card Y = 1 := by
    rw [← map_pow]
    have : uN ^ Nat.card Y = 1 := by
      apply Subtype.ext
      have h := pow_card_eq_one' (G := Y) (x := ⟨u, huY⟩)
      have h' := congrArg Subtype.val h
      rw [Subgroup.coe_pow, Subgroup.coe_one] at h'
      exact h'
    rw [this, map_one]
  have h3 : orderOf (π uN) = 1 := by
    have := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
    rwa [hYc, Nat.dvd_one] at this
  have h4 : π uN = 1 := orderOf_eq_one_iff.1 h3
  have h5 : π zN = 1 := hπz.trans h4
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h5
  exact (Subgroup.mem_subgroupOf).1 h5

theorem i116pI_not_commute_conj {p : ℕ} (hB : IsElemAbelian p B) {x : X} (hxB : x ∈ B)
    (hnz : ∃ j ∈ i116pI_J B L, x * j ≠ j * x) {M : Subgroup X} (hM : i116pI_Conj B L M) :
    ∃ m ∈ M, x * m ≠ m * x := by
  by_contra hcon0
  have hcon : ∀ m ∈ M, Commute x m := fun m hm => by
    by_contra h
    exact hcon0 ⟨m, hm, h⟩
  obtain ⟨g0, hg0, rfl⟩ := hM
  obtain ⟨j, hj, hne⟩ := hnz
  refine hne ?_
  have hle : i116pI_J B L ≤ Subgroup.centralizer ({x} : Set X) := by
    refine iSup₂_le fun g hg m hm => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hw : g0⁻¹ * (g * m * g⁻¹) * g0 ∈ GLBConj g0 L := by
      rw [mem_gLBConj, show g0 * (g0⁻¹ * (g * m * g⁻¹) * g0) * g0⁻¹ = g * m * g⁻¹ by group]
      exact mem_gLBConj.1 hm
    have hxw : Commute x (g0⁻¹ * (g * m * g⁻¹) * g0) := hcon _ hw
    have hc : Commute x (g0⁻¹ * g) := i116pI_comm hB hxB (B.mul_mem (B.inv_mem hg0) hg)
    have hfin : Commute x ((g0⁻¹ * g)⁻¹ * (g0⁻¹ * (g * m * g⁻¹) * g0) * (g0⁻¹ * g)) :=
      (hc.inv_right.mul_right hxw).mul_right hc
    rw [show (g0⁻¹ * g)⁻¹ * (g0⁻¹ * (g * m * g⁻¹) * g0) * (g0⁻¹ * g) = m by group] at hfin
    exact hfin.symm.eq
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hj)).symm

theorem i116pI_conj_Conj [Finite X] {p : ℕ} (hL : IsComponentOf L ⊤) {Y : Subgroup X}
    (hYc : Nat.Coprime p (Nat.card Y)) (hBY : B ≤ Subgroup.normalizer (Y : Set X)) {x : X}
    (hxB : x ∈ B) (hxJ : x ∈ i116pI_J B L) (hxp : x ^ p = 1)
    (h4 : ∀ M, i116pI_Conj B L M → ∃ m ∈ M, x * m ≠ m * x) {y : X} (hy : y ∈ Y)
    {M : Subgroup X} (hM : i116pI_Conj B L M) : i116pI_Conj B L (GLBConj y⁻¹ M) := by
  by_contra hD
  have hMc := i116pI_isComponentOf_conj hL hM
  have hDc : IsComponentOf (GLBConj y⁻¹ M) ⊤ := isComponentOf_gLBConj hMc y⁻¹
  obtain ⟨m, hm, hne⟩ := h4 M hM
  have hz := i116pI_conj_mem_J hL hYc hBY hxB hxJ hxp hy
  have hd : y * m * y⁻¹ ∈ GLBConj y⁻¹ M := by
    rw [mem_gLBConj, inv_inv, show y⁻¹ * (y * m * y⁻¹) * y = m by group]
    exact hm
  have := i116pI_centralizes_J hL hDc hD hd hz
  apply hne
  have h2 : y * (m * x) * y⁻¹ = y * (x * m) * y⁻¹ := by
    calc y * (m * x) * y⁻¹ = (y * m * y⁻¹) * (y * x * y⁻¹) := by group
      _ = (y * x * y⁻¹) * (y * m * y⁻¹) := this
      _ = y * (x * m) * y⁻¹ := by group
  have h3 := mul_left_cancel (mul_right_cancel h2)
  exact h3.symm

end Basic

section Layer

variable {X : Type*} [Group X]

theorem i116pI_pcomp_card_dvd [Finite X] {p : ℕ} (hp : p.Prime) {C K : Subgroup X}
    (hK : GLAPComponent p C K) : p ∣ Nat.card K := by
  by_contra hndvd
  have hcop : Nat.Coprime p (Nat.card K) := (Nat.Prime.coprime_iff_not_dvd hp).2 hndvd
  have h1 : K ≤ GLAPPrimeCoreOf p C := by
    rw [← glaPPrimeCoreOf_eq_self_of_coprime hcop]
    exact glaPPrimeCoreOf_le_of_isSubnormal hp hK.2.1
  have h2 : barX p C K = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨k, hk, rfl⟩
    have hk' : k ∈ K.subgroupOf C := hk
    rw [Subgroup.mem_subgroupOf] at hk'
    obtain ⟨c, hc, hck⟩ := h1 hk'
    have : c = k := Subtype.ext hck
    subst this
    simpa using (QuotientGroup.eq_one_iff (N := GLAPPrimeCore p ↥C) c).2 hc
  have hnt : Nontrivial (barX p C K) := CFSG.ComponentClassification.Quasisimple.nontrivial hK.2.2.1.2.2
  exact (Subgroup.nontrivial_iff_ne_bot _).1 hnt h2

theorem i116pI_layer_le (p : ℕ) (C : Subgroup X) : GLAPLayer p C ≤ C :=
  sSup_le fun _ hK => hK.1

theorem i116pI_layer_facts [Finite X] {p : ℕ} (hp : p.Prime) {C : Subgroup X}
    (hne : GLAPLayer p C ≠ ⊥) :
    p ∣ Nat.card (GLAPLayer p C) ∧ ∃ a ∈ GLAPLayer p C, ∃ b ∈ GLAPLayer p C, a * b ≠ b * a := by
  have hK : ∃ K, GLAPComponent p C K ∧ K ≠ ⊥ := by
    by_contra hcon
    refine hne (sSup_eq_bot.2 fun K hK => ?_)
    by_contra hK'
    exact hcon ⟨K, hK, hK'⟩
  obtain ⟨K, hK, hKne⟩ := hK
  have hKle : K ≤ GLAPLayer p C := le_sSup hK
  refine ⟨(i116pI_pcomp_card_dvd hp hK).trans (Subgroup.card_dvd_of_le hKle), ?_⟩
  by_contra hcon
  have hcomm : ∀ a ∈ GLAPLayer p C, ∀ b ∈ GLAPLayer p C, a * b = b * a := by
    intro a ha b hb
    by_contra h
    exact hcon ⟨a, ha, b, hb, h⟩
  have h1 : ⁅K, K⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro a ha b hb
    have := hcomm a (hKle ha) b (hKle hb)
    rw [Subgroup.mem_bot, commutatorElement_def, this]
    group
  exact hKne (by rw [← glaPComponent_perfect hK, h1])

theorem i116pI_mem_normalizer_layer (p : ℕ) {C : Subgroup X} {g : X}
    (hg : g ∈ Subgroup.normalizer (C : Set X)) :
    g ∈ Subgroup.normalizer (GLAPLayer p C : Set X) := by
  have key : ∀ g ∈ Subgroup.normalizer (C : Set X),
      GLBConj g (GLAPLayer p C) ≤ GLAPLayer p C := by
    intro g hg
    have hC : GLBConj g C = C := mem_normalizer_iff_gLBConj_eq.1 hg
    have h1 : GLBConj g (GLAPLayer p C) =
        ⨆ K ∈ {L | GLAPComponent p C L}, GLBConj g K := by
      unfold GLAPLayer GLBConj
      rw [sSup_eq_iSup, Subgroup.map_iSup]
      simp only [Subgroup.map_iSup]
    rw [h1]
    refine iSup₂_le fun K hK => ?_
    have := glaPComponent_gLBConj hK g
    rw [hC] at this
    exact le_sSup this
  rw [mem_normalizer_iff_gLBConj_eq]
  exact i116pI_gLBConj_eq_of_le (key g hg) (key g⁻¹ ((Subgroup.normalizer _).inv_mem hg))

theorem i116pI_mem_normalizer_inf {A A' : Subgroup X} {g : X}
    (h : g ∈ Subgroup.normalizer (A : Set X)) (h' : g ∈ Subgroup.normalizer (A' : Set X)) :
    g ∈ Subgroup.normalizer ((A ⊓ A' : Subgroup X) : Set X) := by
  rw [Subgroup.mem_normalizer_iff] at h h' ⊢
  intro z
  rw [Subgroup.mem_inf, Subgroup.mem_inf, h z, h' z]

theorem i116pI_exists_x [Finite X] {p : ℕ} (hp : p.Prime) {B L : Subgroup X}
    (hB : IsSCp p ⊤ B) {b : X} (hb : b ∈ B)
    (hs : IsSimpleGroup ↥(GLAPLayer p (Subgroup.centralizer ({b} : Set X) ⊓ i116pI_J B L))) :
    ∃ x ∈ B, x ≠ 1 ∧ x ^ p = 1 ∧ x ∈ i116pI_J B L ∧
      ∃ j ∈ i116pI_J B L, x * j ≠ j * x := by
  have : Fact p.Prime := ⟨hp⟩
  set C : Subgroup X := Subgroup.centralizer ({b} : Set X) ⊓ i116pI_J B L with hC
  set Jo : Subgroup X := GLAPLayer p C with hJo
  have hBC : ∀ g ∈ B, g ∈ Subgroup.normalizer (C : Set X) := by
    intro g hg
    refine i116pI_mem_normalizer_inf (Subgroup.le_normalizer ?_) (i116pI_mem_normalizer_J hg)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (i116pI_comm hB.2.1 hb hg).symm ▸ rfl
  have hBJo : B ≤ Subgroup.normalizer (Jo : Set X) :=
    fun g hg => i116pI_mem_normalizer_layer p (hBC g hg)
  have hne : Jo ≠ ⊥ := by
    have : Nontrivial ↥Jo := hs.toNontrivial
    exact (Subgroup.nontrivial_iff_ne_bot _).1 this
  obtain ⟨hdvd, a, ha, c, hc, hac⟩ := i116pI_layer_facts hp hne
  obtain ⟨x, hx, hx1⟩ := exists_ne_one_mem_inf_of_isSCp hB hBJo hdvd
  have hxJ : x ∈ i116pI_J B L := ((i116pI_layer_le p C) hx.2).2
  refine ⟨x, hx.1, hx1, hB.2.1.2 x hx.1, hxJ, ?_⟩
  by_contra hcon
  have hcomm : ∀ j ∈ i116pI_J B L, x * j = j * x := by
    intro j hj
    by_contra h
    exact hcon ⟨j, hj, h⟩
  have hJoJ : Jo ≤ i116pI_J B L := (i116pI_layer_le p C).trans inf_le_right
  let xo : ↥Jo := ⟨x, hx.2⟩
  have hxo : xo ∈ Subgroup.center ↥Jo := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcomm g.1 (hJoJ g.2)).symm
  rcases (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥Jo)) with h | h
  · rw [h, Subgroup.mem_bot] at hxo
    exact hx1 (congrArg Subtype.val hxo)
  · have hmem : (⟨c, hc⟩ : ↥Jo) ∈ Subgroup.center ↥Jo := h ▸ Subgroup.mem_top _
    rw [Subgroup.mem_center_iff] at hmem
    exact hac (congrArg Subtype.val (hmem ⟨a, ha⟩))

end Layer

section Action

variable {X : Type*} [Group X]

@[expose, instance_reducible] def i116pI_act (X : Type*) [Group X] : MulAction X (Subgroup X) where
  smul g M := GLBConj g⁻¹ M
  one_smul M := by
    show GLBConj (1 : X)⁻¹ M = M
    rw [inv_one, gLBConj_one]
  mul_smul g h M := by
    show GLBConj (g * h)⁻¹ M = GLBConj g⁻¹ (GLBConj h⁻¹ M)
    rw [gLBConj_gLBConj, mul_inv_rev]

attribute [local instance] i116pI_act

theorem i116pI_smul_def (g : X) (M : Subgroup X) : g • M = GLBConj g⁻¹ M := rfl

theorem i116pI_smul_sub (K : Subgroup X) (g : K) (M : Subgroup X) :
    g • M = GLBConj (g : X)⁻¹ M := rfl

theorem i116pI_mem_orbit_iff {B : Subgroup X} {L M : Subgroup X} :
    M ∈ MulAction.orbit ↥B L ↔ i116pI_Conj B L M := by
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨(b : X)⁻¹, B.inv_mem b.2, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g⁻¹, B.inv_mem hg⟩, by
      show GLBConj (g⁻¹)⁻¹ L = GLBConj g L
      rw [inv_inv]⟩

theorem i116pI_stabilizer_eq (B L : Subgroup X) :
    MulAction.stabilizer ↥B L = (Subgroup.normalizer (L : Set X)).subgroupOf B := by
  ext b
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, i116pI_smul_sub,
    ← inv_mem_iff (x := (b : X)), mem_normalizer_iff_gLBConj_eq]

theorem i116pI_final [Finite X] {p : ℕ} {B L Y : Subgroup X}
    (hidx : (Subgroup.normalizer (L : Set X)).relIndex B = p)
    (hYc : Nat.Coprime p (Nat.card Y)) (hBY : B ≤ Subgroup.normalizer (Y : Set X))
    (h6 : ∀ y ∈ Y, ∀ M, i116pI_Conj B L M → i116pI_Conj B L (GLBConj y⁻¹ M)) :
    Y ≤ Subgroup.normalizer (L : Set X) := by
  set H : Subgroup X := Y ⊔ B with hH
  have hYH : Y ≤ H := le_sup_left
  have hBH : B ≤ H := le_sup_right
  have hclos : ∀ h ∈ H, (∀ M, i116pI_Conj B L M → i116pI_Conj B L (GLBConj h⁻¹ M)) ∧
      (∀ M, i116pI_Conj B L M → i116pI_Conj B L (GLBConj h M)) := by
    intro h hh
    rw [hH, Subgroup.sup_eq_closure] at hh
    induction hh using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · refine ⟨h6 x hx, fun M hM => ?_⟩
        have := h6 x⁻¹ (Y.inv_mem hx) M hM
        rwa [inv_inv] at this
      · refine ⟨fun M hM => ?_, fun M hM => ?_⟩
        · obtain ⟨g, hg, rfl⟩ := hM
          exact ⟨g * x⁻¹, B.mul_mem hg (B.inv_mem hx), by rw [gLBConj_gLBConj]⟩
        · obtain ⟨g, hg, rfl⟩ := hM
          exact ⟨g * x, B.mul_mem hg hx, by rw [gLBConj_gLBConj]⟩
    | one =>
      refine ⟨fun M hM => ?_, fun M hM => ?_⟩ <;> simpa [gLBConj_one] using hM
    | mul a b _ _ ha hb =>
      refine ⟨fun M hM => ?_, fun M hM => ?_⟩
      · have := ha.1 _ (hb.1 M hM)
        rwa [gLBConj_gLBConj, ← mul_inv_rev] at this
      · have := hb.2 _ (ha.2 M hM)
        rwa [gLBConj_gLBConj] at this
    | inv a _ ha =>
      refine ⟨fun M hM => ?_, fun M hM => ?_⟩
      · simpa using ha.2 M hM
      · simpa using ha.1 M hM
  have horb : MulAction.orbit ↥H L = MulAction.orbit ↥B L := by
    ext M
    constructor
    · rintro ⟨h, rfl⟩
      rw [i116pI_mem_orbit_iff]
      exact (hclos h h.2).1 L ⟨1, B.one_mem, (gLBConj_one L).symm⟩
    · rintro ⟨b, rfl⟩
      exact ⟨⟨b, hBH b.2⟩, rfl⟩
  have hBcard : (MulAction.orbit ↥B L).ncard = p := by
    rw [← MulAction.index_stabilizer, i116pI_stabilizer_eq]
    exact hidx
  have hΩ : Nat.card (↥H ⧸ MulAction.stabilizer ↥H L) = p := by
    rw [← hBcard, ← horb, ← MulAction.index_stabilizer]
    rfl
  have hHnorm : (Y.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYH).2 (sup_le Subgroup.le_normalizer hBY)
  have hcop : Nat.Coprime p (Nat.card (Y.subgroupOf H)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYH).toEquiv]
  intro y hy
  have h1 := smul_eq_of_normal_coprime hΩ (Y.subgroupOf H) hcop (⟨y, hYH hy⟩ : ↥H)
    ((Subgroup.mem_subgroupOf).2 hy) (QuotientGroup.mk (1 : ↥H) : ↥H ⧸ MulAction.stabilizer ↥H L)
  have h2 : (⟨y, hYH hy⟩ : ↥H) ∈ MulAction.stabilizer ↥H L := by
    have h3 : (⟨y, hYH hy⟩ : ↥H) • (QuotientGroup.mk (1 : ↥H) : ↥H ⧸ MulAction.stabilizer ↥H L) =
        ((⟨y, hYH hy⟩ : ↥H) : ↥H ⧸ MulAction.stabilizer ↥H L) := by
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
    rw [h3] at h1
    have := (QuotientGroup.eq (a := (⟨y, hYH hy⟩ : ↥H)) (b := 1)).1 h1
    simpa using this
  rw [MulAction.mem_stabilizer_iff, i116pI_smul_sub] at h2
  have h4 : (y : X)⁻¹ ∈ Subgroup.normalizer (L : Set X) :=
    mem_normalizer_iff_gLBConj_eq.2 h2
  simpa using h4

end Action

theorem partI (hK : Kernel11_2) {X : Type} [Group X] [Finite X] (hX : IsKGroup X) {p : ℕ}
    (hp : p.Prime) (hodd : p ≠ 2) (hO : GLAPPrimeCore p X = ⊥) {B : Subgroup X}
    (hB : IsSCp p ⊤ B) (hrank : GLATwoLocalRank p X ≤ pRank p B) {Y : Subgroup X}
    (hYc : Nat.Coprime p (Nat.card Y)) (hBY : B ≤ Subgroup.normalizer (Y : Set X))
    {L : Subgroup X} (hL : GLAPComponent p ⊤ L) (hnL : ¬ B ≤ Subgroup.normalizer (L : Set X)) :
    Y ≤ Subgroup.normalizer (L : Set X) := by
  obtain ⟨hidx, hsimple⟩ := hK X hX p hp hodd hO B hB.2.1 hrank L hL hnL
  have hLc : IsComponentOf L ⊤ := i116pI_isComponentOf hO hL
  obtain ⟨b, hb, hbn⟩ := IsConcreteLE.not_le_iff_exists.1 hnL
  obtain ⟨x, hxB, hx1, hxp, hxJ, hnz⟩ := i116pI_exists_x hp hB hb (hsimple b hb hbn)
  have h4 : ∀ M, i116pI_Conj B L M → ∃ m ∈ M, x * m ≠ m * x :=
    fun M hM => i116pI_not_commute_conj hB.2.1 hxB hnz hM
  exact i116pI_final hidx hYc hBY fun y hy M hM =>
    i116pI_conj_Conj hLc hYc hBY hxB hxJ hxp h4 hy hM

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance
