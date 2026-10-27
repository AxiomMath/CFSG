module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm3QuotEdge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm3Quot

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Orbit

variable {Y : Type} [Group Y] [Finite Y]

theorem le_conjStab_orbit (Y₀ M : Subgroup Y) :
    Y₀ ≤ conjStab {L : Subgroup Y | ∃ y ∈ Y₀, L = conjSub y M} := by
  intro y₀ hy₀ L
  constructor
  · rintro ⟨y, hy, hyL⟩
    refine ⟨y₀⁻¹ * y, Y₀.mul_mem (Y₀.inv_mem hy₀) hy, ?_⟩
    rw [conjSub_mul, ← hyL, conjSub_inv_conjSub]
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y₀ * y, Y₀.mul_mem hy₀ hy, (conjSub_mul _ _ _).symm⟩

theorem mem_conjStab_of_forall_fix {O : Set (Subgroup Y)} {g : Y}
    (h : ∀ L ∈ O, conjSub g L = L) : g ∈ conjStab O := by
  intro L
  constructor
  · intro hL
    have h3 : conjSub g L = L := conjSub_injective g (h _ hL)
    rw [← h3]
    exact hL
  · intro hL
    rw [h L hL]
    exact hL

theorem orderOf_conj_eq (y g : Y) : orderOf (y⁻¹ * g * y) = orderOf g := by
  have := orderOf_injective (MulAut.conj y⁻¹).toMonoidHom (MulAut.conj y⁻¹).injective g
  simpa using this

theorem conjSub_eq_of_odd_of_twinSet_pair {Φ : Set (Subgroup Y)} (hc : ConjInvariant Φ)
    {M Mstar : Subgroup Y} (hM : M ∈ Φ) {z : Y} (hz : IsUniqueInvolution M z)
    (htw : twinSet Φ M = {M, Mstar}) {h : Y} (hh : Odd (orderOf h)) (hhz : h * z * h⁻¹ = z) :
    conjSub h M = M := by
  have hMs : Mstar ∈ twinSet Φ M := by rw [htw]; exact Or.inr rfl
  obtain ⟨hMsΦ, z', hz'M, hz'Ms⟩ := hMs
  have hzs : IsUniqueInvolution Mstar z := (hz.eq hz'M) ▸ hz'Ms
  have hmem : ∀ L, L ∈ Φ → IsUniqueInvolution L z → conjSub h L ∈ ({M, Mstar} : Set _) := by
    intro L hL hzL
    rw [← htw]
    refine ⟨hc h L hL, z, hz, ?_⟩
    have := hzL.conj h
    rwa [hhz] at this
  rcases hmem M hM hz with h1 | h1
  · exact h1
  · rcases hmem Mstar hMsΦ hzs with h2 | h2
    · rw [h1]
      exact (eq_of_odd_swap_conjSub hh h1 h2).symm
    · have := conjSub_injective h (h1.trans h2.symm)
      rw [h1, ← this]

theorem mem_conjStab_orbit_of_odd {M Z Y₀ : Subgroup Y} {z : Y} (hzZ : z ∈ Z)
    (hY₀ : Y₀ ≤ Subgroup.normalizer (Z : Set Y))
    (hfix : ∀ h : Y, Odd (orderOf h) → h * z * h⁻¹ = z → conjSub h M = M) {g : Y}
    (hg : Odd (orderOf g)) (hgZ : g ∈ Subgroup.centralizer (Z : Set Y)) :
    g ∈ conjStab {L : Subgroup Y | ∃ y ∈ Y₀, L = conjSub y M} := by
  refine mem_conjStab_of_forall_fix ?_
  rintro _ ⟨y, hy, rfl⟩
  have hyz : y * z * y⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp (hY₀ hy) z).mp hzZ
  have hgyz : g * (y * z * y⁻¹) * g⁻¹ = y * z * y⁻¹ := by
    have := Subgroup.mem_centralizer_iff.mp hgZ _ hyz
    rw [← this]
    group
  have hh : Odd (orderOf (y⁻¹ * g * y)) := by rw [orderOf_conj_eq]; exact hg
  have hhz : (y⁻¹ * g * y) * z * (y⁻¹ * g * y)⁻¹ = z := by
    calc (y⁻¹ * g * y) * z * (y⁻¹ * g * y)⁻¹ = y⁻¹ * (g * (y * z * y⁻¹) * g⁻¹) * y := by group
      _ = z := by rw [hgyz]; group
  have hM := hfix _ hh hhz
  calc conjSub g (conjSub y M) = conjSub y (conjSub (y⁻¹ * g * y) M) := by
        rw [← conjSub_mul, ← conjSub_mul]
        congr 1
        group
    _ = conjSub y M := by rw [hM]

end Orbit

section Lift

variable {Y : Type} [Group Y] [Finite Y] {Φ : Set (Subgroup Y)} {X : Subgroup Y} [X.Normal]

theorem eq_of_mem_of_map_eq (hX : Odd (Nat.card X)) {Z : Subgroup Y} (hZ : IsPGroup 2 Z)
    {a b : Y} (ha : a ∈ Z) (hb : b ∈ Z)
    (h : QuotientGroup.mk' X a = QuotientGroup.mk' X b) : a = b := by
  have hZX : Z ⊓ X = ⊥ :=
    AscQuot.inf_eq_bot_of_isPGroup_of_odd X hZ le_rfl (odd_natCard_inf hX Z)
  have h1 : a⁻¹ * b ∈ Z ⊓ X := ⟨Z.mul_mem (Z.inv_mem ha) hb, OddQuot.inv_mul_mem_of_mk_eq h⟩
  rw [hZX, Subgroup.mem_bot] at h1
  calc a = a * (a⁻¹ * b) := by rw [h1, mul_one]
    _ = b := by group

theorem exists_mul_mem_normalizer_of_map (hX : Odd (Nat.card X)) {Z : Subgroup Y}
    (hZ : IsPGroup 2 Z) {m : Y}
    (hm : QuotientGroup.mk' X m ∈ Subgroup.normalizer
      ((Z.map (QuotientGroup.mk' X) : Subgroup (Y ⧸ X)) : Set (Y ⧸ X))) :
    ∃ n ∈ X, n * m ∈ Subgroup.normalizer (Z : Set Y) := by
  have hZX : Z ⊓ X = ⊥ :=
    AscQuot.inf_eq_bot_of_isPGroup_of_odd X hZ le_rfl (odd_natCard_inf hX Z)
  have hle : conjSub m Z ≤ X ⊔ Z := by
    intro x hx
    have h2 : (conjSub m Z).map (QuotientGroup.mk' X) = Z.map (QuotientGroup.mk' X) := by
      rw [AscQuot.map_conjSub]
      exact mem_normalizer_iff_conjSub_eq.mp hm
    have h1 : QuotientGroup.mk' X x ∈ Z.map (QuotientGroup.mk' X) := by
      rw [← h2]
      exact Subgroup.mem_map_of_mem _ hx
    have h3 : x ∈ (Z.map (QuotientGroup.mk' X)).comap (QuotientGroup.mk' X) := h1
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_comm] at h3
    exact h3
  obtain ⟨n, hn, hnZ⟩ := Q3T7M.CentQ.exists_conjSub_of_le_sup_odd
    (fun g _ => mem_normalizer_of_normal X g) hX hZX hZ (hZ.map _) (AscL62.natCard_conjSub m Z) hle
  have hnZ' : conjSub n Z = conjSub m Z := hnZ
  refine ⟨n⁻¹, X.inv_mem hn, ?_⟩
  rw [mem_normalizer_iff_conjSub_eq, conjSub_mul, ← hnZ', conjSub_inv_conjSub]

theorem mem_conjStab_orbit_of_mem (hΦ : HypOmegaGen Φ) (hX : Odd (Nat.card X))
    {A Z : Subgroup Y} {O : Set (Subgroup Y)} (hA : A ∈ Φ) {a : Y} (ha : IsUniqueInvolution A a)
    (hAO : A ⊓ Subgroup.normalizer (Z : Set Y) ≤ conjStab O)
    (hodd : ∀ g : Y, Odd (orderOf g) → g ∈ Subgroup.normalizer (Z : Set Y) →
      g * a * g⁻¹ = a → g ∈ conjStab O) {g : Y}
    (hg : g ∈ (A ⊔ (X ⊓ Subgroup.centralizer ({a} : Set Y))) ⊓ Subgroup.normalizer (Z : Set Y)) :
    g ∈ conjStab O := by
  set D : Subgroup Y := X ⊓ Subgroup.centralizer ({a} : Set Y) with hDdef
  have hDodd : Odd (Nat.card D) := hX.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hDA : D ≤ Subgroup.normalizer (A : Set Y) := le_normalizer_of_le_centralizer hΦ hX hA ha
  have hAC : A ≤ Subgroup.centralizer ({a} : Set Y) := by
    intro x hx
    have h1 := ha.conj_eq (conjSub_eq_self_of_mem hx)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * a = (x * a * x⁻¹) * x := by group
      _ = a * x := by rw [h1]
  have hADC : A ⊔ D ≤ Subgroup.centralizer ({a} : Set Y) := sup_le hAC inf_le_right
  refine mem_of_forall_pow g (fun k hk => ?_) (fun k hk => ?_)
  · have hgk : g ^ k ∈ (A ⊔ D) ⊓ Subgroup.normalizer (Z : Set Y) := Subgroup.pow_mem _ hg k
    exact hAO ⟨mem_of_isPGroup_of_mem_sup hDodd hDA hgk.1 hk, hgk.2⟩
  · have hgk : g ^ k ∈ (A ⊔ D) ⊓ Subgroup.normalizer (Z : Set Y) := Subgroup.pow_mem _ hg k
    have hca : g ^ k * a * (g ^ k)⁻¹ = a := by
      have := Subgroup.mem_centralizer_singleton_iff.mp (hADC hgk.1)
      rw [this, mul_inv_cancel_right]
    exact hodd _ hk hgk.2 hca

theorem map_inf_normalizer_le_map (hX : Odd (Nat.card X)) {A Z : Subgroup Y} (hZ : IsPGroup 2 Z)
    {a : Y} (ha : IsUniqueInvolution A a) (haZ : a ∈ Z) :
    A.map (QuotientGroup.mk' X) ⊓ Subgroup.normalizer
        ((Z.map (QuotientGroup.mk' X) : Subgroup (Y ⧸ X)) : Set (Y ⧸ X)) ≤
      ((A ⊔ (X ⊓ Subgroup.centralizer ({a} : Set Y))) ⊓
        Subgroup.normalizer (Z : Set Y)).map (QuotientGroup.mk' X) := by
  rintro _ ⟨⟨m, hm, rfl⟩, hmN⟩
  obtain ⟨n, hn, hnm⟩ := exists_mul_mem_normalizer_of_map hX hZ hmN
  have hmn1 : QuotientGroup.mk' X n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
  have hma : m * a * m⁻¹ = a := ha.conj_eq (conjSub_eq_self_of_mem hm)
  have hga : (n * m) * a * (n * m)⁻¹ = n * a * n⁻¹ := by
    calc (n * m) * a * (n * m)⁻¹ = n * (m * a * m⁻¹) * n⁻¹ := by group
      _ = n * a * n⁻¹ := by rw [hma]
  have hgaZ : (n * m) * a * (n * m)⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp hnm a).mp haZ
  have hna : n * a * n⁻¹ = a := by
    rw [← hga]
    refine eq_of_mem_of_map_eq hX hZ hgaZ haZ ?_
    rw [hga, map_mul, map_mul, map_inv, hmn1, one_mul, inv_one, mul_one]
  have hnC : n ∈ Subgroup.centralizer ({a} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc n * a = (n * a * n⁻¹) * n := by group
      _ = a * n := by rw [hna]
  refine ⟨n * m, ⟨Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨hn, hnC⟩)
    (Subgroup.mem_sup_left hm), hnm⟩, ?_⟩
  rw [map_mul, hmn1, one_mul]

abbrev pairLift (X M J : Subgroup Y) (z j : Y) : Subgroup Y :=
  ((M ⊔ (X ⊓ Subgroup.centralizer ({z} : Set Y))) ⊓
      Subgroup.normalizer ((Subgroup.closure ({z, j} : Set Y) : Subgroup Y) : Set Y)) ⊔
    ((J ⊔ (X ⊓ Subgroup.centralizer ({j} : Set Y))) ⊓
      Subgroup.normalizer ((Subgroup.closure ({z, j} : Set Y) : Subgroup Y) : Set Y))

theorem pairNormalizers_map_le (hX : Odd (Nat.card X)) {M J : Subgroup Y} {z j : Y}
    (hz : IsUniqueInvolution M z) (hj : IsUniqueInvolution J j) (hzj : z * j = j * z) :
    pairNormalizers (M.map (QuotientGroup.mk' X)) (J.map (QuotientGroup.mk' X))
        (QuotientGroup.mk' X z) (QuotientGroup.mk' X j) ≤
      (pairLift X M J z j).map (QuotientGroup.mk' X) := by
  have hZ2 := isPGroup_closure_pair hz.sq hj.sq hzj
  have hzZ : z ∈ Subgroup.closure ({z, j} : Set Y) := Subgroup.subset_closure (by simp)
  have hjZ : j ∈ Subgroup.closure ({z, j} : Set Y) := Subgroup.subset_closure (by simp)
  have hZb : Subgroup.closure ({QuotientGroup.mk' X z, QuotientGroup.mk' X j} : Set (Y ⧸ X)) =
      (Subgroup.closure ({z, j} : Set Y)).map (QuotientGroup.mk' X) := by
    rw [MonoidHom.map_closure, Set.image_pair]
  unfold pairNormalizers
  rw [hZb, Subgroup.map_sup]
  exact sup_le_sup (map_inf_normalizer_le_map hX hZ2 hz hzZ)
    (map_inf_normalizer_le_map hX hZ2 hj hjZ)

theorem odd_elt_centralizes_pair {z j g : Y} (hz : z * z = 1) (hj : j * j = 1)
    (hzj : z * j = j * z) (hz1 : z ≠ 1) (hne : z ≠ j)
    (hgZ : g ∈ Subgroup.normalizer ((Subgroup.closure ({z, j} : Set Y) : Subgroup Y) : Set Y))
    (hgz : g * z * g⁻¹ = z) (hg : Odd (orderOf g)) :
    g ∈ Subgroup.centralizer ((Subgroup.closure ({z, j} : Set Y) : Subgroup Y) : Set Y) :=
  mem_centralizer_closure_pair hgz (conj_eq_of_odd_of_fix hz hj hzj hz1 hne hgZ hgz hg)

theorem conj_orbit_pairNormalizers (hΦ : HypOmegaGen Φ) (hX : Odd (Nat.card X))
    {M J : Subgroup Y} {z j : Y} (hM : M ∈ Φ) (hv : AViol Φ M J z j) :
    pairLift X M J z j ≤
      conjStab {L : Subgroup Y | ∃ y ∈ pairNormalizers M J z j, L = conjSub y M} := by
  have hJΦ : J ∈ Φ := hv.mem
  have hz := hv.hzK
  have hj := hv.hzJ
  have hzj : z * j = j * z := aViol_involution_comm hΦ hv
  have hne : z ≠ j := aViol_involution_ne hΦ hM hv
  set Z : Subgroup Y := Subgroup.closure ({z, j} : Set Y) with hZdef
  have hzZ : z ∈ Z := Subgroup.subset_closure (by simp)
  set Y₀ : Subgroup Y := pairNormalizers M J z j with hY₀def
  set O : Set (Subgroup Y) := {L | ∃ y ∈ Y₀, L = conjSub y M} with hOdef
  have hY₀Z : Y₀ ≤ Subgroup.normalizer (Z : Set Y) := sup_le inf_le_right inf_le_right
  have hInA : InA Φ M J :=
    ⟨hv.star, hv.not_nbr, z, j, hz, hj, fun ⟨g, hg, hgK⟩ => hv.no_conj g hg hgK⟩
  obtain ⟨-, -, -, -, Mstar, -, -, -, -, -, -, -, -, -, -, -, -, -, -, htw, -⟩ :=
    Sec6Gen.l6_4ThreeGen Y Φ hΦ M hM J hJΦ hInA z j hz hj _ _ rfl rfl
  have hfix : ∀ h : Y, Odd (orderOf h) → h * z * h⁻¹ = z → conjSub h M = M :=
    fun h hh hhz => conjSub_eq_of_odd_of_twinSet_pair hΦ.conjInvariant hM hz htw hh hhz
  have hY₀O : Y₀ ≤ conjStab O := le_conjStab_orbit Y₀ M
  have hcent : ∀ g : Y, Odd (orderOf g) → g ∈ Subgroup.centralizer (Z : Set Y) →
      g ∈ conjStab O :=
    fun g hg hgZ => mem_conjStab_orbit_of_odd hzZ hY₀Z hfix hg hgZ
  have hZ' : Subgroup.closure ({j, z} : Set Y) = Z := by rw [hZdef, Set.pair_comm]
  have hoddM : ∀ g : Y, Odd (orderOf g) → g ∈ Subgroup.normalizer (Z : Set Y) →
      g * z * g⁻¹ = z → g ∈ conjStab O := fun g hg hgZ hgz =>
    hcent g hg (odd_elt_centralizes_pair hz.sq hj.sq hzj hz.ne_one hne hgZ hgz hg)
  have hoddJ : ∀ g : Y, Odd (orderOf g) → g ∈ Subgroup.normalizer (Z : Set Y) →
      g * j * g⁻¹ = j → g ∈ conjStab O := by
    intro g hg hgZ hgj
    have hgZ' : g ∈ Subgroup.normalizer
        ((Subgroup.closure ({j, z} : Set Y) : Subgroup Y) : Set Y) := by rw [hZ']; exact hgZ
    have h1 := odd_elt_centralizes_pair hj.sq hz.sq hzj.symm hj.ne_one (Ne.symm hne) hgZ' hgj hg
    rw [hZ'] at h1
    exact hcent g hg h1
  have hMO : M ⊓ Subgroup.normalizer (Z : Set Y) ≤ conjStab O :=
    le_trans (le_sup_left : M ⊓ _ ≤ Y₀) hY₀O
  have hJO : J ⊓ Subgroup.normalizer (Z : Set Y) ≤ conjStab O :=
    le_trans (le_sup_right : J ⊓ _ ≤ Y₀) hY₀O
  exact sup_le (fun g hg => mem_conjStab_orbit_of_mem hΦ hX hM hz hMO hoddM hg)
    (fun g hg => mem_conjStab_orbit_of_mem hΦ hX hJΦ hj hJO hoddJ hg)

theorem aViol_map_no_conj (hΦ : HypOmegaGen Φ) (hX : Odd (Nat.card X)) {M J : Subgroup Y}
    {z j : Y} (hM : M ∈ Φ) (hv : AViol Φ M J z j) :
    ∀ g ∈ pairNormalizers (M.map (QuotientGroup.mk' X)) (J.map (QuotientGroup.mk' X))
        (QuotientGroup.mk' X z) (QuotientGroup.mk' X j),
      conjSub g (M.map (QuotientGroup.mk' X)) ≠ J.map (QuotientGroup.mk' X) := by
  have hJΦ : J ∈ Φ := hv.mem
  have hz := hv.hzK
  have hj := hv.hzJ
  have hzj : z * j = j * z := aViol_involution_comm hΦ hv
  set Z : Subgroup Y := Subgroup.closure ({z, j} : Set Y) with hZdef
  have hZ2 : IsPGroup 2 Z := isPGroup_closure_pair hz.sq hj.sq hzj
  have hzZ : z ∈ Z := Subgroup.subset_closure (by simp)
  have hjZ : j ∈ Z := Subgroup.subset_closure (by simp)
  have hY₁Z : pairLift X M J z j ≤ Subgroup.normalizer (Z : Set Y) :=
    sup_le inf_le_right inf_le_right
  intro gb hgb hconj
  obtain ⟨g, hgY₁, rfl⟩ := pairNormalizers_map_le hX hz hj hzj hgb
  have hgO := conj_orbit_pairNormalizers hΦ hX hM hv hgY₁
  have hgZ := hY₁Z hgY₁
  have hMO' : M ∈ {L : Subgroup Y | ∃ y ∈ pairNormalizers M J z j, L = conjSub y M} :=
    ⟨1, Subgroup.one_mem _, (conjSub_one M).symm⟩
  obtain ⟨y, hy, hyM⟩ := (mem_conjStab_iff.mp hgO M).mpr hMO'
  have himg : (conjSub g M).map (QuotientGroup.mk' X) = J.map (QuotientGroup.mk' X) := by
    rw [AscQuot.map_conjSub]
    exact hconj
  have hgz : g * z * g⁻¹ = j := by
    have hgzZ : g * z * g⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp hgZ z).mp hzZ
    refine eq_of_mem_of_map_eq hX hZ2 hgzZ hjZ ?_
    have h1 := isUniqueInvolution_map_mk_of_odd
      (odd_natCard_inf hX (conjSub g M)) (hz.conj g)
    rw [himg] at h1
    exact h1.eq (isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hX J) hj)
  have hzg : IsUniqueInvolution (conjSub g M) j := by
    have := hz.conj g
    rwa [hgz] at this
  have heq : conjSub g M = J :=
    eq_of_map_eq_of_inv_eq hΦ hX (hΦ.conjInvariant g M hM) hJΦ hzg hj himg
  exact hv.no_conj y hy (hyM ▸ heq)

theorem aViol_map (hΦ : HypOmegaGen Φ) (hX : Odd (Nat.card X)) {M J : Subgroup Y} {z j : Y}
    (hM : M ∈ Φ) (hv : AViol Φ M J z j) :
    AViol (quotFamily Φ X) (M.map (QuotientGroup.mk' X)) (J.map (QuotientGroup.mk' X))
      (QuotientGroup.mk' X z) (QuotientGroup.mk' X j) where
  star := by
    obtain ⟨-, hne⟩ := map_ne_of_aViol hΦ hX hM hv
    refine (omegaStarNbr_map_iff hΦ hX hv.mem hM hne).mpr ⟨1, X.one_mem, ?_⟩
    rw [conjSub_one]
    exact hv.star
  not_nbr := not_omegaNbr_map_of_aSet hΦ hX hM ⟨z, j, hv⟩
  hzK := isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hX M) hv.hzK
  hzJ := isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hX J) hv.hzJ
  no_conj := aViol_map_no_conj hΦ hX hM hv

theorem aSet_map (hΦ : HypOmegaGen Φ) (hX : Odd (Nat.card X)) {M J : Subgroup Y} (hM : M ∈ Φ)
    (hJ : J ∈ aSet Φ M) :
    J.map (QuotientGroup.mk' X) ∈ aSet (quotFamily Φ X) (M.map (QuotientGroup.mk' X)) := by
  obtain ⟨z, j, hv⟩ := hJ
  exact ⟨_, _, aViol_map hΦ hX hM hv⟩

theorem not_aEmpty_map (hΦ : HypOmegaGen Φ) (hX : Odd (Nat.card X)) {K : Subgroup Y}
    (hK : K ∈ Φ) (hA : ¬ AEmpty Φ K) :
    ¬ AEmpty (quotFamily Φ X) (K.map (QuotientGroup.mk' X)) := by
  obtain ⟨J, zK, zJ, hv⟩ := not_aEmpty_iff.mp hA
  exact not_aEmpty_iff.mpr ⟨_, _, _, aViol_map hΦ hX hK hv⟩

end Lift

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm3Quot

