module

public import CFSG.Alternating.Multipliers.OddKernel
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.CanonicalHeart
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56.BridgeGN
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.BlockLift
public import CFSG.LocalAnalysis.RankThreeUC.GN15AltBaumMod

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.GN
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56
  CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542 CFSG.AGLEmbedding CFSG.RankThree.PartTwo Equiv
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry (altHeart_fixed_eq_zero)
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

section Lift

@[expose] def compMk (L : Subgroup (X ⧸ gnC T)) :
    ↥(L.comap (QuotientGroup.mk' (gnC T))) →* ↥L :=
  ((QuotientGroup.mk' (gnC T)).comp (L.comap (QuotientGroup.mk' (gnC T))).subtype).codRestrict L
    (fun k => k.2)

omit [Finite X] in
theorem compMk_surjective (L : Subgroup (X ⧸ gnC T)) : Function.Surjective (compMk (T := T) L) :=
  fun l => by
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (l : X ⧸ gnC T)
    exact ⟨⟨x, by
      show QuotientGroup.mk' (gnC T) x ∈ L
      rw [show QuotientGroup.mk' (gnC T) x = (l : X ⧸ gnC T) from hx]; exact l.2⟩,
      Subtype.ext hx⟩

@[expose] def liftToAlt (L : Subgroup (X ⧸ gnC T)) {n : ℕ} (g : ↥L →* alternatingGroup (Fin n)) :
    ↥(L.comap (QuotientGroup.mk' (gnC T))) →* alternatingGroup (Fin n) :=
  g.comp (compMk L)

omit [Finite X] in
theorem liftToAlt_surjective (L : Subgroup (X ⧸ gnC T)) {n : ℕ}
    {g : ↥L →* alternatingGroup (Fin n)} (hg : Function.Surjective g) :
    Function.Surjective (liftToAlt L g) := hg.comp (compMk_surjective L)

omit [Finite X] in
theorem liftToAlt_eq_one_iff (L : Subgroup (X ⧸ gnC T)) {n : ℕ}
    {g : ↥L →* alternatingGroup (Fin n)} (hgi : Function.Injective g)
    (k : ↥(L.comap (QuotientGroup.mk' (gnC T)))) :
    liftToAlt L g k = 1 ↔ (k : X) ∈ gnC T := by
  constructor
  · intro h
    have h1 : compMk L k = 1 := hgi (h.trans (map_one g).symm)
    have h2 : QuotientGroup.mk' (gnC T) (k : X) = 1 := congrArg Subtype.val h1
    exact (QuotientGroup.eq_one_iff _).1 h2
  · intro h
    have : compMk L k = 1 := Subtype.ext ((QuotientGroup.eq_one_iff _).2 h)
    show g (compMk L k) = 1
    rw [this, map_one]

end Lift

section Adaptor

omit [Finite X] in
theorem exists_altBaumSection_of_setup {V₀ K : Subgroup X} {n : ℕ} (hn : 9 ≤ n) (hodd : Odd n)
    {Φ : ↥K →* alternatingGroup (Fin n)} (hS : AltBaumSetup V₀ K Φ)
    {π : ↥⁅V₀, K⁆ →* Multiplicative (altHeart n)} (hπs : Function.Surjective π)
    (hπk : ∀ u, π u = 1 → ∀ k ∈ K, (k : X) * u * (k : X)⁻¹ = u)
    (hπi : ∀ (l : ↥K) (u u' : ↥⁅V₀, K⁆), (u' : X) = l * u * l⁻¹ → ∀ x : evenWeight n,
      Multiplicative.toAdd (π u) = (QuotientAddGroup.mk x : altHeart n) →
      Multiplicative.toAdd (π u') =
        (QuotientAddGroup.mk (evenWeightPerm (Φ l : Perm (Fin n)) x) : altHeart n)) :
    ∃ π' : ↥⁅V₀, K⁆ →* Multiplicative (evenWeight n), AltBaumSection V₀ K Φ π' := by
  classical
  let ε : evenWeight n ≃+ altHeart n :=
    AddEquiv.ofBijective (QuotientAddGroup.mk' (evenWeightOnes n))
      ⟨altHeart_mk_injective hodd, QuotientAddGroup.mk_surjective⟩
  let ε' : Multiplicative (altHeart n) ≃* Multiplicative (evenWeight n) :=
    AddEquiv.toMultiplicative ε.symm
  let π' : ↥⁅V₀, K⁆ →* Multiplicative (evenWeight n) := ε'.toMonoidHom.comp π
  refine ⟨π', ⟨ε'.surjective.comp hπs, fun u => ?_, fun l u u' h => ?_⟩⟩
  · rw [show π' u = ε' (π u) from rfl, MulEquiv.map_eq_one_iff]
    refine ⟨fun h1 => hπk u h1, fun hfix => ?_⟩
    obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd (π u))
    have hfixv : ∀ σ ∈ alternatingGroup (Fin n),
        (QuotientAddGroup.mk (evenWeightPerm σ x) : altHeart n) = QuotientAddGroup.mk x := by
      intro σ hσ
      obtain ⟨k, hk⟩ := hS.surj ⟨σ, hσ⟩
      have h2 : (Φ k : Perm (Fin n)) = σ := congrArg Subtype.val hk
      have h3 := hπi k u u (hfix k k.2).symm x hx.symm
      rw [h2] at h3
      rw [← h3, hx]
    have h0 := altHeart_fixed_eq_zero (by omega) x hfixv
    rw [hx] at h0
    exact Multiplicative.toAdd.injective (h0.trans toAdd_one.symm)
  · have hx : Multiplicative.toAdd (π u) =
        (QuotientAddGroup.mk (Multiplicative.toAdd (π' u)) : altHeart n) := by
      show _ = ε (ε.symm (Multiplicative.toAdd (π u)))
      rw [ε.apply_symm_apply]
    have h1 := hπi l u u' h _ hx
    show ε.symm (Multiplicative.toAdd (π u')) = _
    rw [h1]
    exact ε.symm_apply_apply _

theorem altBaumSetup_gnV (hX : GNSetting X T) {K : Subgroup X} {n : ℕ}
    {Φ : ↥K →* alternatingGroup (Fin n)} (hΦs : Function.Surjective Φ)
    (hΦk : ∀ k : ↥K, Φ k = 1 ↔ (k : X) ∈ gnC T) : AltBaumSetup (gnV T) K Φ := by
  have hVel : IsElemAbelian 2 (gnV T) := isElemAbelian_gnV T hX
  have := normal_gnV (X := X) T
  have hVC : ∀ c ∈ gnC T, ∀ v ∈ gnV T, c * v * c⁻¹ = v := fun c hc v hv => by
    have h1 : v * c = c * v := Subgroup.mem_centralizer_iff.1 hc v hv
    rw [← h1, mul_inv_cancel_right]
  exact
    { comm := fun v hv w hw => congrArg Subtype.val (hVel.1.is_comm.comm ⟨v, hv⟩ ⟨w, hw⟩)
      sq := fun v hv => by have := hVel.2 v hv; simpa [pow_two] using this
      norm := fun k _ v hv => ‹(gnV T).Normal›.conj_mem v hv k
      surj := hΦs
      ker := fun k hk v hv => hVC _ ((hΦk k).1 hk) v hv }

end Adaptor

section A2

private theorem injective_of_surjective_of_odd_center {P : Type*} [Group P] [Finite P]
    [Group.IsPerfect P] {n : ℕ} (hn : 8 ≤ n) (g : P →* alternatingGroup (Fin n))
    (hg : Function.Surjective g) (hker : g.ker ≤ Subgroup.center P)
    (hodd : Odd (Nat.card (Subgroup.center P))) : Function.Injective g := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have h1 := CFSG.Alternating.Multipliers.card_ker_eq_one_of_odd (by omega) g hg hker
    (Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le hker))
  exact (injective_iff_map_eq_one g).2 fun x hx =>
    Subgroup.mem_bot.1 ((Subgroup.eq_bot_of_card_eq _ h1) ▸ (MonoidHom.mem_ker.2 hx))

theorem injective_of_surjective_component (hX : GNSetting X T) {L : Subgroup (X ⧸ gnC T)}
    (hL : IsComponentOf L ⊤) {n : ℕ} (hn : 8 ≤ n) {g : ↥L →* alternatingGroup (Fin n)}
    (hg : Function.Surjective g) : Function.Injective g := by
  have hq : CFSG.IsQuasisimple ↥L := B1Red.isQuasisimple_of_open hL.2.2
  have hgnt : ∃ l : ↥L, g l ≠ 1 := by
    obtain ⟨a, b, hab⟩ := (alternatingGroup.isSimpleGroup
      (by rw [Nat.card_fin]; omega : 5 ≤ Nat.card (Fin n))).toNontrivial.exists_pair_ne
    by_contra h
    push Not at h
    obtain ⟨la, rfl⟩ := hg a
    obtain ⟨lb, rfl⟩ := hg b
    exact hab ((h la).trans (h lb).symm)
  have hkerc : g.ker ≤ Subgroup.center ↥L :=
    CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hq hgnt
  have : Group.IsPerfect ↥L := hq.1
  have hoddc : Odd (Nat.card (Subgroup.center ↥L)) :=
    Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 (not_two_dvd_card_center hX hL))
  exact injective_of_surjective_of_odd_center hn g hg hkerc hoddc

end A2

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
