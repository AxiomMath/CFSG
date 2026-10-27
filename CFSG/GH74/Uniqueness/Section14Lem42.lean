module

public import CFSG.GH74.Uniqueness.Section123
public import CFSG.GH74.Uniqueness.Section122Bender

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

namespace Sec14

theorem n_odd {c : Ctx12 Z M} {n : ℕ} (h : LData c n 2) : Odd n ∧ 3 ≤ n := by
  rcases h.bender.cases' with ⟨hi, -, -⟩ | ⟨-, -, a, ha, hn⟩ | ⟨hi, -, -⟩
  · omega
  · subst hn
    exact ⟨⟨a, by ring⟩, by omega⟩
  · omega

theorem not_solvable_L {c : Ctx12 Z M} {n i : ℕ} (h : LData c n i) :
    ¬ Group.IsSolvable ↥c.L := by
  intro hsol
  have : IsSimpleGroup ↥c.L := h.bender.isSimple
  exact h.bender.isSimpleBenderGroup.not_commutative
    ((IsSimpleGroup.comm_iff_isSolvable (G := ↥c.L)).mpr hsol)

theorem zHull_eq_L_of_le
    (S : ZDSetup X Z M) {c : Ctx12 Z M} {n : ℕ} (h : LData c n 2)
    {F : Subgroup X} (hF : F ≠ ⊤) (hLF : c.L ≤ F) : zHull Z F = c.L := by
  have hZ := S.invariant
  have hLv : c.L ≤ zHull Z F := by
    calc c.L = zHull Z c.L := (S.zHull_L c).symm
      _ ≤ zHull Z F := closure_mono (fun x hx => ⟨hx.1, hLF hx.2⟩)
  have hFM : ¬ F ≤ M := fun hle => c.htM (hle (hLF c.t_mem_L))
  have hne : (Z ∩ ((F ⊓ M : Subgroup X) : Set X)).Nonempty :=
    ⟨c.z, c.hz, mem_inf.mpr ⟨hLF c.z_mem_L, c.hzM⟩⟩
  have hns : ¬ Group.IsSolvable ↥(zHull Z F) := by
    intro hsol
    exact not_solvable_L h (Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion hLv) (Subgroup.inclusion_injective hLv))
  obtain ⟨n', i', e', hB⟩ := S.benderSub_exists hF hFM hne hns
  have hZM : Z ∩ ((zHull Z F ⊓ M : Subgroup X) : Set X) = Z ∩ (M : Set X) := by
    ext x
    constructor
    · rintro ⟨hxZ, hxLM⟩
      exact ⟨hxZ, (mem_inf.mp hxLM).2⟩
    · rintro ⟨hxZ, hxM⟩
      refine ⟨hxZ, mem_inf.mpr ⟨hLv ?_, hxM⟩⟩
      exact IsProductDisconnected.inter_le_lSubgroup hZ S.prodDisc c.ht c.htM c.hz c.hzM
        ⟨hxZ, hxM⟩
  have hn : n' = n := by
    have h1 := A2.ncard_inter_of_benderSub S hB
    rw [hZM, A2.ncard_zM h] at h1
    have h2 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have h3 : 1 ≤ 2 ^ n' := Nat.one_le_two_pow
    exact Nat.pow_right_injective le_rfl (by omega : 2 ^ n' = 2 ^ n)
  subst n'
  have hcL : center ↥c.L = ⊥ := h.center_eq_bot
  let ι : ↥c.L →* ↥(zHull Z F) ⧸ center ↥(zHull Z F) :=
    (QuotientGroup.mk' (center ↥(zHull Z F))).comp (Subgroup.inclusion hLv)
  have hιinj : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro l hl
    have hmem : Subgroup.inclusion hLv l ∈ center ↥(zHull Z F) :=
      (QuotientGroup.eq_one_iff _).mp hl
    have hlc : l ∈ center ↥c.L := by
      rw [mem_center_iff]
      intro g
      apply Subtype.ext
      have h1 := congrArg Subtype.val (mem_center_iff.mp hmem (Subgroup.inclusion hLv g))
      exact h1
    rw [hcL, mem_bot] at hlc
    exact hlc
  rcases Bender.BenderType.embedding_index h.bender hB.bender ι hιinj with hii | ⟨hi1, -⟩
  ·
    subst hii
    have he' : e' = 1 := by
      rcases hB.bender.cases' with ⟨-, he, -⟩ | ⟨-, he, -⟩ | ⟨hi3, -, -⟩
      · exact he
      · exact he
      · omega
    subst he'
    have hcard : Nat.card (↥(zHull Z F) ⧸ center ↥(zHull Z F)) ≤ Nat.card ↥c.L := by
      rw [h.bender.card_eq, hB.bender.card_eq]
    have hsurj : Function.Surjective ι := (hιinj.bijective_of_nat_card_le hcard).2
    have hodd := A2.odd_card_center_of_benderSub hB
    refine le_antisymm ((closure_le _).mpr ?_) hLv
    rintro s ⟨hsZ, hsF⟩
    have hsF' : s ∈ zHull Z F := subset_closure ⟨hsZ, hsF⟩
    obtain ⟨l, hl⟩ := hsurj (QuotientGroup.mk' (center ↥(zHull Z F)) ⟨s, hsF'⟩)
    have hc : (Subgroup.inclusion hLv l)⁻¹ * ⟨s, hsF'⟩ ∈ center ↥(zHull Z F) :=
      QuotientGroup.eq.mp hl
    have hss : (⟨s, hsF'⟩ : ↥(zHull Z F)) * ⟨s, hsF'⟩ = 1 :=
      Subtype.ext (hZ.mul_self_eq_one hsZ)
    set a : ↥(zHull Z F) := Subgroup.inclusion hLv l with ha
    set o : ↥(zHull Z F) := a⁻¹ * ⟨s, hsF'⟩ with ho
    have hbo : (⟨s, hsF'⟩ : ↥(zHull Z F)) = a * o := by
      rw [ho, mul_inv_cancel_left]
    have hoa : a * o = o * a := mem_center_iff.mp hc a
    have h1 : (a * a) * (o * o) = 1 := by
      rw [← hss]
      conv_rhs => rw [hbo]
      calc (a * a) * (o * o) = a * (a * o) * o := by group
        _ = a * (o * a) * o := by rw [hoa]
        _ = (a * o) * (a * o) := by group
    have haa : a * a ∈ center ↥(zHull Z F) := by
      rw [eq_inv_of_mul_eq_one_left h1]
      exact (center _).inv_mem ((center _).mul_mem hc hc)
    have hll : l * l = 1 := by
      apply hιinj
      rw [map_mul, map_one]
      change QuotientGroup.mk' (center ↥(zHull Z F)) a *
        QuotientGroup.mk' (center ↥(zHull Z F)) a = 1
      rw [← map_mul]
      exact (QuotientGroup.eq_one_iff _).mpr haa
    have haa1 : a * a = 1 := by
      rw [ha, ← map_mul, hll, map_one]
    rw [haa1, one_mul] at h1
    have ho1 := eq_one_of_mem_of_sq_eq_one hodd hc h1
    have hsl : (⟨s, hsF'⟩ : ↥(zHull Z F)) = a := by
      rw [hbo, ho1, mul_one]
    have hsl' : s = (l : X) := congrArg Subtype.val hsl
    rw [SetLike.mem_coe, hsl']
    exact l.2
  · omega

theorem isSimple
    (S : ZDSetup X Z M) : IsSimpleGroup X := S.theorem1_unconditional.1

theorem normalizer_le_of_le_J
    (S : ZDSetup X Z M) {c : Ctx12 Z M} {n : ℕ} (h : LData c n 2)
    {Y : Subgroup X} (hYJ : Y ≤ centralizer (c.L : Set X)) (hY : Y ≠ ⊥) :
    normalizer (Y : Set X) ≤ normalizer (c.L : Set X) := by
  have hYM : Y ≤ M := hYJ.trans (h.centralizer_le.trans inf_le_left)
  have hF : normalizer (Y : Set X) ≠ ⊤ := by
    intro htop
    have hYn : Y.Normal := normalizer_eq_top_iff.mp htop
    have : IsSimpleGroup X := isSimple S
    rcases Subgroup.Normal.eq_bot_or_eq_top Y with h1 | h1
    · exact hY h1
    · exact S.prodDisc.1 (top_le_iff.mp (h1 ▸ hYM))
  have hLF : c.L ≤ normalizer (Y : Set X) :=
    (le_centralizer_iff.mp hYJ).trans (centralizer_le_normalizer _)
  have hz := zHull_eq_L_of_le S h hF hLF
  have := le_normalizer_zHull S.invariant (normalizer (Y : Set X))
  rwa [hz] at this

theorem centralizer_le_of_mem_J
    (S : ZDSetup X Z M) {c : Ctx12 Z M} {n : ℕ} (h : LData c n 2)
    {v : X} (hv : v ∈ centralizer (c.L : Set X)) (hv1 : v ≠ 1) :
    centralizer ({v} : Set X) ≤ normalizer (c.L : Set X) := by
  have hY : zpowers v ≤ centralizer (c.L : Set X) := zpowers_le.mpr hv
  have hY1 : zpowers v ≠ ⊥ := by
    intro h0
    apply hv1
    have := mem_zpowers v
    rw [h0, mem_bot] at this
    exact this
  refine le_trans ?_ (normalizer_le_of_le_J S h hY hY1)
  intro x hx
  apply centralizer_le_normalizer
  rw [mem_centralizer_iff]
  intro y hy
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
  have hc : Commute v x := (mem_centralizer_singleton_iff.mp hx).symm
  exact (hc.zpow_left k).eq

theorem cenHull_eq_L
    (S : ZDSetup X Z M) {c : Ctx12 Z M} {n : ℕ} (h : LData c n 2) {v : X}
    (hv : v ∈ centralizer (c.L : Set X)) (hv1 : v ≠ 1) : cenHull Z v = c.L :=
  zHull_eq_L_of_le S h (A2.centralizer_ne_top S hv1)
    (fun y hy => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hv y hy))

omit [Finite X] in
theorem conj_mem_cenHull (hZ : IsInvariantInvolutionSet Z) {v x : X} (g : X)
    (hx : x ∈ cenHull Z v) : g * x * g⁻¹ ∈ cenHull Z (g * v * g⁻¹) := by
  have hle : cenHull Z v ≤ (cenHull Z (g * v * g⁻¹)).comap (MulAut.conj g).toMonoidHom := by
    rw [cenHull, zHull, closure_le]
    rintro y ⟨hyZ, hyC⟩
    rw [SetLike.mem_coe, mem_comap]
    have e : (MulAut.conj g).toMonoidHom y = g * y * g⁻¹ := by simp
    rw [e]
    refine subset_closure ⟨?_, ?_⟩
    · have := hZ.2 y hyZ g⁻¹
      rwa [inv_inv] at this
    · rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hyC ⊢
      calc g * y * g⁻¹ * (g * v * g⁻¹) = g * (y * v) * g⁻¹ := by group
        _ = g * (v * y) * g⁻¹ := by rw [hyC]
        _ = _ := by group
  have := hle hx
  simpa using this

theorem mem_normalizer_of_conj_J
    (S : ZDSetup X Z M) {c : Ctx12 Z M} {n : ℕ} (h : LData c n 2)
    {v w g : X} (hv : v ∈ centralizer (c.L : Set X)) (hv1 : v ≠ 1)
    (hw : w ∈ centralizer (c.L : Set X)) (hw1 : w ≠ 1) (hg : g * v * g⁻¹ = w) :
    g ∈ normalizer (c.L : Set X) := by
  have h1 : ∀ x ∈ c.L, g * x * g⁻¹ ∈ c.L := by
    intro x hx
    rw [← cenHull_eq_L S h hv hv1] at hx
    have := conj_mem_cenHull S.invariant g hx
    rwa [hg, cenHull_eq_L S h hw hw1] at this
  have h2 : ∀ x ∈ c.L, g⁻¹ * x * g ∈ c.L := by
    intro x hx
    have hg' : g⁻¹ * w * g⁻¹⁻¹ = v := by rw [← hg]; group
    rw [← cenHull_eq_L S h hw hw1] at hx
    have := conj_mem_cenHull S.invariant g⁻¹ hx
    rw [hg', cenHull_eq_L S h hv hv1] at this
    simpa using this
  rw [mem_normalizer_iff]
  intro x
  refine ⟨h1 x, fun hx => ?_⟩
  have := h2 _ hx
  simpa [mul_assoc] using this

theorem exists_involution_D (c : Ctx12 Z M) : ∃ u ∈ c.D, orderOf u = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥c.D) 2 (even_iff_two_dvd.mp c.hD)
  exact ⟨u, u.2, by rw [Subgroup.orderOf_coe]; exact hu⟩

theorem mem_J_of_involution (h12 : Sec12Results Z M) {c : Ctx12 Z M} {n : ℕ} (h : LData c n 2)
    {u : X} (hu : u ∈ c.D) (hu2 : orderOf u = 2) : u ∈ centralizer (c.L : Set X) := by
  obtain ⟨-, hb, -⟩ := h12.l124 c n 2 h u hu hu2
  rcases hb with hb | ⟨h1, -⟩
  · rw [mem_centralizer_iff]
    intro y hy
    exact hb y hy
  · omega

theorem exists_injective_J (h12 : Sec12Results Z M) (h131 : Prop131Stmt Z M) {c : Ctx12 Z M}
    {n : ℕ} (h : LData c n 2) :
    ∃ f : ↥(centralizer (c.L : Set X)) →* ↥c.L, Function.Injective f := by
  obtain ⟨u, hu, hu2⟩ := exists_involution_D c
  exact (h12.l1214 c n 2 h u hu hu2 (h131 c n 2 h u hu hu2)).2

end Sec14

end CFSG.GH74.Uniqueness
