module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUnitaryParam
public import CFSG.LieType.CurtisTits.Unitary

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive)
open CFSG.LieType.CurtisTits (rankOne levi)
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

theorem exists_plane_off_ctu {N m : ℕ} (hN : 5 ≤ N) (J : Finset (Fin m)) (hJ : J.card ≤ 2) :
    ∃ k : Fin N, ∀ j ∈ J, k.val ≠ j.val ∧ k.val ≠ j.val + 1 := by
  classical
  set bad : Finset ℕ := J.image (fun j => j.val) ∪ J.image (fun j => j.val + 1) with hbad
  have hcard : bad.card < (Finset.range N).card := by
    rw [Finset.card_range]
    calc bad.card ≤ (J.image (fun j => j.val)).card + (J.image (fun j => j.val + 1)).card :=
          Finset.card_union_le _ _
      _ ≤ J.card + J.card := add_le_add Finset.card_image_le Finset.card_image_le
      _ < N := by omega
  obtain ⟨k, hk, hkb⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  refine ⟨⟨k, Finset.mem_range.1 hk⟩, fun j hj => ⟨fun h => hkb ?_, fun h => hkb ?_⟩⟩
  · exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨j, hj, h.symm⟩)
  · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨j, hj, h.symm⟩)

theorem levi_le_ctuBlock {F : Type} [Field F] {σ : F ≃+* F} {hσ : ∀ c, σ (σ c) = c} {N ε : ℕ}
    (hε : ε ≤ 1) {J : Finset (Fin ((2 * N + ε) / 2))} {k : Fin N}
    (hk : ∀ j ∈ J, k.val ≠ j.val ∧ k.val ≠ j.val + 1) :
    levi (rootGroup σ hσ (2 * N + ε)) J ≤ ctuBlock σ ε ({k} : Finset (Fin N)) :=
  iSup₂_le fun j hj => rankOne_le_ctuBlock hε j (hk j hj).1 (hk j hj).2

theorem odd_card_center_SU {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) {n : ℕ} (hn : 3 ≤ n)
    (hnq : (n, 2 ^ f) ≠ (3, 2)) :
    Odd (Nat.card (center (SU (unitaryInvolution F 2 f) n))) := by
  have hF' : Nat.card F = 2 ^ (2 * f) := by rw [hF, ← pow_mul, mul_comm]
  have hodd := odd_card_units_of_card_eq_two_pow hF' (by omega)
  rw [Nat.odd_iff]
  by_contra h
  have h2 : 2 ∣ Nat.card (center (SU (unitaryInvolution F 2 f) n)) := by omega
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
  obtain ⟨c, hc⟩ := exists_scalar_of_mem_center_SU hF hn hnq z.2
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hinj : Function.Injective (GeneralLinearGroup.scalar (Fin n) (R := F)) := by
    intro a b hab
    have := congrArg (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F) ⟨0, by omega⟩
      ⟨0, by omega⟩) hab
    simp only [GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq] at this
    exact Units.ext this
  have h1 : orderOf c = 2 := by
    rw [← orderOf_injective _ hinj c, ← hc, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
  have h3 := Odd.of_dvd_nat hodd (h1 ▸ orderOf_dvd_natCard c)
  exact absurd h3 (by decide)

theorem eq_of_rootTorusHom_of_tau {K : Type} [Field K] {N : ℕ} {G : Type*} [Group G]
    (φ ψ : StatedSp N K →* G)
    (hτ : ∀ (j : Fin N) (hj : j.val + 1 < N) (κ : Kˣ),
      φ (diagSp K N (Pi.mulSingle j κ * Pi.mulSingle ⟨j.val + 1, hj⟩ κ⁻¹)) =
        ψ (diagSp K N (Pi.mulSingle j κ * Pi.mulSingle ⟨j.val + 1, hj⟩ κ⁻¹)))
    (hlast : ∀ j : Fin N, j.val + 1 = N → ∀ κ : Kˣ,
      φ (rootTorusHom K N j κ) = ψ (rootTorusHom K N j κ))
    (k : Fin N) (κ : Kˣ) : φ (rootTorusHom K N k κ) = ψ (rootTorusHom K N k κ) := by
  obtain ⟨d, hd⟩ : ∃ d, d = N - 1 - k.val := ⟨_, rfl⟩
  induction d generalizing k with
  | zero => exact hlast k (by have := k.2; omega) κ
  | succ d ih =>
    have hk1 : k.val + 1 < N := by omega
    have hsplit : rootTorusHom K N k κ = diagSp K N (Pi.mulSingle k κ *
        Pi.mulSingle ⟨k.val + 1, hk1⟩ κ⁻¹) * rootTorusHom K N ⟨k.val + 1, hk1⟩ κ := by
      rw [rootTorusHom_apply, rootTorusHom_apply, ← map_mul, mul_assoc, ← Pi.mulSingle_mul,
        inv_mul_cancel, Pi.mulSingle_one, mul_one]
    rw [hsplit, map_mul φ, map_mul ψ, hτ k hk1 κ, ih ⟨k.val + 1, hk1⟩ (by simp only; omega)]

theorem diagSp_mem_spBlock_compl_of_eq_one {K : Type} [Field K] {N : ℕ} {t : Fin N → Kˣ}
    {k : Fin N} (ht : t k = 1) : diagSp K N t ∈ spBlock K ({k} : Finset (Fin N))ᶜ := by
  have h : Function.update t k 1 = t := by
    rw [← ht]
    exact Function.update_eq_self k t
  rw [← h]
  exact diagSp_update_mem_spBlock_compl t k

section Recognition

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]
  [CharP K 2] {N ε : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} {hε : ε ≤ 1}
  {ι : K →+* F} {hι : ∀ c, unitaryInvolution F 2 f (ι c) = ι c} {e : L ≃* StatedSp N K}

theorem exists_ct_uniRow_of_agree (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hN : 5 ≤ N)
    (hF : Nat.card F = (2 ^ f) ^ 2)
    (P : ∀ k : Fin N, CtuParam ε hε (unitaryInvolution F 2 f) ι hι e k)
    (hagree : CtuParamAgree P) :
    ∃ ψ : SU (unitaryInvolution F 2 f) (2 * N + ε) →* G, ψ.range = spGlobal e ∧
      ψ.ker ≤ center (SU (unitaryInvolution F 2 f) (2 * N + ε)) ∧
      CFSG.IsQuasisimple (spGlobal e) ∧ Odd (Nat.card (center (spGlobal e))) ∧
      LieModel (spGlobal e ⧸ center (spGlobal e)) .PSU (2 * N + ε) 2 f := by
  classical
  have hK4 : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  have hn3 : 3 ≤ 2 * N + ε := by omega
  have hnq : (2 * N + ε, 2 ^ f) ≠ (3, 2) := fun h => by
    have := (Prod.mk.inj h).1
    omega
  set σ := unitaryInvolution F 2 f with hσdef
  set D := rootDatum hF (2 * N + ε) with hD
  have hrank : D.rank = (2 * N + ε) / 2 := rfl
  have hdiv : (2 * N + ε) / 2 = N := by omega
  choose kJ hkJ using fun J : {J : Finset (Fin D.rank) // J.card ≤ 2} =>
    exists_plane_off_ctu (N := N) hN J.1 J.2
  have hKle : ∀ J : {J : Finset (Fin D.rank) // J.card ≤ 2},
      D.leviAmalgam J ≤ ctuBlock σ ε ({kJ J} : Finset (Fin N)) :=
    fun J => levi_le_ctuBlock hε (hkJ J)
  set φ : ∀ J, D.leviAmalgam J →* G := fun J => (P (kJ J)).Φ.comp (Subgroup.inclusion (hKle J))
    with hφ
  have hφapp : ∀ J (x : D.leviAmalgam J), φ J x = (P (kJ J)).Φ ⟨x, hKle J x.2⟩ :=
    fun _ _ => rfl
  have hcomp : CFSG.LieType.CurtisTits.IsCompatible D.leviAmalgam φ := by
    intro I J _ x y hxy
    rw [hφapp, hφapp]
    have hy' : (x : SU σ (2 * N + ε)) ∈ ctuBlock σ ε ({kJ J} : Finset (Fin N)) := by
      rw [hxy]
      exact hKle J y.2
    rw [hagree (kJ I) (kJ J) _ (hKle I x.2) hy']
    congr 2
  set G₀ : Subgroup G := ⨆ J, (φ J).range with hG₀
  have hle : ∀ J x, φ J x ∈ G₀ := fun J x => le_iSup (fun J => (φ J).range) J ⟨x, rfl⟩
  set φ' : ∀ J, D.leviAmalgam J →* G₀ := fun J => (φ J).codRestrict G₀ (hle J) with hφ'
  have hcomp' : CFSG.LieType.CurtisTits.IsCompatible D.leviAmalgam φ' :=
    fun I J hIJ x y hxy => Subtype.ext (hcomp I J hIJ x y hxy)
  have hgen' : ⨆ J, (φ' J).range = ⊤ := by
    apply Subgroup.map_injective G₀.subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    refine (iSup_congr fun J => ?_).trans hG₀.symm
    rw [← MonoidHom.range_comp]
    rfl
  have htau : ∀ (j : Fin D.rank) (y : StatedSp N K)
      (hy : ctuEmbed ε hε σ ι hι y ∈ rankOne D.rootGroup j)
      (hys : ∀ k : Fin N, k.val ≠ j.val → k.val ≠ j.val + 1 →
        y ∈ spBlock K ({k} : Finset (Fin N))ᶜ),
      ∃ (J : {J : Finset (Fin D.rank) // J.card ≤ 2}) (x : D.leviAmalgam J),
        (x : SU σ (2 * N + ε)) = ctuEmbed ε hε σ ι hι y ∧ φ J x = ((e.symm y : L) : G) := by
    intro j y hy hys
    set J : {J : Finset (Fin D.rank) // J.card ≤ 2} := ⟨{j}, by simp⟩ with hJ
    have hxJ : ctuEmbed ε hε σ ι hι y ∈ D.leviAmalgam J :=
      CFSG.LieType.CurtisTits.rankOne_le_levi _ (Finset.mem_singleton_self j) hy
    refine ⟨J, ⟨_, hxJ⟩, rfl, ?_⟩
    rw [hφapp]
    obtain ⟨h1, h2⟩ := hkJ J j (Finset.mem_singleton_self j)
    exact (P (kJ J)).N1' (hys _ h1 h2) _ rfl
  have hnt : ∃ J, ∃ x, φ' J x ≠ 1 := by
    obtain ⟨κ, hκ⟩ := exists_units_mul_self_ne_one_of_four_le hK4
    have hκ1 : κ ≠ 1 := fun h => hκ (by rw [h, one_mul])
    have h0 : (0 : ℕ) + 1 < (2 * N + ε) / 2 := by omega
    obtain ⟨J, x, -, hφx⟩ := htau ⟨0, by omega⟩ _
      (ctuEmbed_shortTorus_mem_rankOne hF hε (ι := ι) (hι := hι) (j := ⟨0, by omega⟩) h0 κ)
      (fun k hk1 hk2 => diagSp_mem_spBlock_compl_of_eq_one (by
        have hk1' : k ≠ ⟨0, by omega⟩ := fun h => hk1 (by rw [h])
        have hk2' : k ≠ ⟨0 + 1, by omega⟩ := fun h => hk2 (by rw [h])
        rw [Pi.mul_apply, Pi.mulSingle_eq_of_ne hk1', Pi.mulSingle_eq_of_ne hk2', mul_one]))
    refine ⟨J, x, fun h => ?_⟩
    have h1 : φ J x = 1 := congrArg Subtype.val h
    rw [hφx] at h1
    have h2 : e.symm (diagSp K N (Pi.mulSingle (⟨0, by omega⟩ : Fin N) κ *
        Pi.mulSingle ⟨0 + 1, by omega⟩ κ⁻¹)) = 1 := Subtype.ext h1
    rw [MulEquiv.map_eq_one_iff] at h2
    have h3 := congrFun (diagSp_injective (h2.trans (map_one _).symm)) ⟨0, by omega⟩
    have hne : (⟨0, by omega⟩ : Fin N) ≠ ⟨0 + 1, by omega⟩ := fun h => by
      have := congrArg Fin.val h
      simp at this
    rw [Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hne, mul_one] at h3
    exact hκ1 h3
  have hadm : StatedLieAdmissible .PSU (2 * N + ε) 2 f := ⟨Nat.prime_two, by omega, hn3, hnq⟩
  obtain ⟨-, -, hrec, -⟩ :=
    CFSG.LieType.CurtisTits.curtisTitsConclusion_unitary.{0} (F := F) (p := 2) (f := f)
      (n := 2 * N + ε) hadm hF
  obtain ⟨ψ₀, hψ₀, hsurj, hker, hqs, hZ, -, hLM⟩ := hrec G₀ φ' hcomp' hgen' hnt
  set ψ : SU σ (2 * N + ε) →* G := G₀.subtype.comp ψ₀ with hψdef
  have hψrange : ψ.range = G₀ := by
    rw [hψdef, MonoidHom.range_comp, MonoidHom.range_eq_top.2 hsurj, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hψφ : ∀ J (x : D.leviAmalgam J), ψ x = φ J x := fun J x =>
    congrArg Subtype.val (hψ₀ J x)
  have hψker : ψ.ker ≤ center (SU σ (2 * N + ε)) := by
    intro z hz
    apply hker
    rw [MonoidHom.mem_ker] at hz ⊢
    exact G₀.subtype_injective (by rw [map_one]; exact hz)
  have hG₀le : G₀ ≤ spGlobal e := by
    refine iSup_le fun J => ?_
    rintro _ ⟨x, rfl⟩
    rw [hφapp]
    set A : Subgroup (SU σ (2 * N + ε)) := ((spGlobal e).comap (P (kJ J)).Φ).map
      (ctuBlock σ ε ({kJ J} : Finset (Fin N))).subtype with hA
    have hAle : D.leviAmalgam J ≤ A := by
      refine iSup₂_le fun j hj => ?_
      intro y hy
      obtain ⟨h1, h2⟩ := hkJ J j hj
      refine ⟨⟨y, rankOne_le_ctuBlock hε j h1 h2 hy⟩, ?_, rfl⟩
      exact le_iSup (fun j : Fin N => pieceCore e ({j} : Finset (Fin N))) _
        ((P (kJ J)).mem_pieceCore hF hf hn3 j h1 h2 hy)
    obtain ⟨y, hy, hyx⟩ := hAle x.2
    have hyx' : (⟨x, hKle J x.2⟩ : ctuBlock σ ε ({kJ J} : Finset (Fin N))) = y :=
      Subtype.ext hyx.symm
    rw [hyx']
    exact hy
  have htor : ∀ (k : Fin N) (κ : Kˣ), ψ (ctuEmbed ε hε σ ι hι (rootTorusHom K N k κ)) =
      ((e.symm (rootTorusHom K N k κ) : L) : G) := by
    intro k κ
    refine eq_of_rootTorusHom_of_tau (ψ.comp (ctuEmbed ε hε σ ι hι))
      (L.subtype.comp e.symm.toMonoidHom) (fun j hj κ => ?_) (fun j hj κ => ?_) k κ
    · have hjr : j.val + 1 < (2 * N + ε) / 2 := by omega
      obtain ⟨J, x, hx, hφx⟩ := htau ⟨j.val, by omega⟩ _
        (ctuEmbed_shortTorus_mem_rankOne hF hε (ι := ι) (hι := hι) (j := ⟨j.val, by omega⟩)
          hjr κ)
        (fun k hk1 hk2 => diagSp_mem_spBlock_compl_of_eq_one (by
          have hk1' : k ≠ ⟨j.val, by omega⟩ := fun h => hk1 (by rw [h])
          have hk2' : k ≠ ⟨j.val + 1, by omega⟩ := fun h => hk2 (by rw [h])
          rw [Pi.mul_apply, Pi.mulSingle_eq_of_ne hk1', Pi.mulSingle_eq_of_ne hk2', mul_one]))
      change ψ (ctuEmbed ε hε σ ι hι _) = ((e.symm _ : L) : G)
      rw [← hx, hψφ J x, hφx]
    · have hjr : ¬(j.val + 1 < (2 * N + ε) / 2) := by omega
      obtain ⟨J, x, hx, hφx⟩ := htau ⟨j.val, by omega⟩ _
        (ctuEmbed_rootTorusHom_mem_rankOne hF hε (ι := ι) (hι := hι) (j := ⟨j.val, by omega⟩)
          hjr κ)
        (fun k hk1 _ => by
          rw [rootTorusHom_apply]
          exact diagSp_mem_spBlock_compl_of_eq_one (by
            have hk1' : k ≠ ⟨j.val, by omega⟩ := fun h => hk1 (by rw [h])
            rw [Pi.mulSingle_eq_of_ne hk1']))
      change ψ (ctuEmbed ε hε σ ι hι _) = ((e.symm _ : L) : G)
      rw [← hx, hψφ J x, hφx]
  have hEk : ∀ k : Fin N, neighbourCore e k ≤ G₀ := by
    intro k
    set B := ctuBlock σ ε ({k} : Finset (Fin N)) with hB
    set A := perfectCore B with hAdef
    have hAB : A ≤ B := CFSG.Quasithin.perfectCore_le B
    have hk' : k ∈ ({k} : Finset (Fin N)) := Finset.mem_singleton_self k
    have hA1 : A.map ψ ≤ neighbourCore e k := by
      refine CFSG.Quasithin.le_perfectCore_of_perfect ?_ ?_
      · rintro _ ⟨a, ha, rfl⟩
        rw [mem_centralizer_iff]
        intro g hg
        obtain ⟨x, hx, rfl⟩ := (UnitaryPilot.mem_modelToG e).1 hg
        obtain ⟨κ, rfl⟩ := mem_rootTorusSp.1 hx
        have hxs : rootTorusHom K N k κ ∈ spBlock K ({k} : Finset (Fin N)) := by
          rw [spBlock_singleton]
          exact rootTorusSp_le_longRootSp2 k (rootTorusHom_mem_rootTorusSp k κ)
        rw [← htor k κ, ← map_mul, ← map_mul]
        congr 1
        exact (commute_ctuBlock_ctuEmbed (hAB ha) hxs).symm
      · rw [← map_commutator, CFSG.Quasithin.perfectCore_perfect]
    have hcardE : Nat.card (neighbourCore e k) ≤ Nat.card (A.map ψ) := by
      have hinj : Function.Injective (ψ.comp A.subtype) := by
        intro x y hxy
        exact Subtype.ext (injOn_ctuBlock_of_ker_le_center hF hn3 hnq hψker hk' (hAB x.2)
          (hAB y.2) hxy)
      have h1 : Nat.card (A.map ψ) = Nat.card A := by
        have h2 : A.map ψ = (ψ.comp A.subtype).range := by
          rw [MonoidHom.range_comp, range_subtype]
        rw [h2]
        exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
      have hEperf : perfectCore (neighbourCore e k) = neighbourCore e k :=
        CFSG.Quasithin.perfectCore_eq_self_of_perfect
          (F4Pilot.commutator_centralizerPerfectCore _)
      have h3 : neighbourCore e k = (perfectCore (⊤ : Subgroup B)).map (P k).Φ := by
        rw [CFSG.Quasithin.map_perfectCore, ← MonoidHom.range_eq_map, (P k).range_eq, hEperf]
      have h4 : (perfectCore (⊤ : Subgroup B)).map B.subtype = A := by
        rw [CFSG.Quasithin.map_perfectCore, ← MonoidHom.range_eq_map, range_subtype]
      rw [h1, h3, ← h4, Subgroup.card_map_of_injective B.subtype_injective]
      exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ _)
    have heq := Subgroup.eq_of_le_of_card_ge hA1 hcardE
    rw [← heq, ← hψrange]
    rintro _ ⟨a, -, rfl⟩
    exact ⟨a, rfl⟩
  have hG₀eq : G₀ = spGlobal e := le_antisymm hG₀le
    ((spGlobal_le_iSup_neighbourCore (by omega) e).trans (iSup_le hEk))
  clear_value G₀
  subst hG₀eq
  refine ⟨ψ, hψrange, hψker, hqs, ?_, hLM⟩
  rw [hZ]
  exact Odd.of_dvd_nat (odd_card_center_SU hF (by omega) hn3 hnq) (Subgroup.card_map_dvd _ _)

theorem spGlobalCoverType_of_ctuParamAgree (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hN : 5 ≤ N)
    (hF : Nat.card F = (2 ^ f) ^ 2) {κ : Sp2mKind}
    (hκ : (κ = .unitaryEven ∧ ε = 0) ∨ (κ = .unitaryOdd ∧ ε = 1))
    (P : ∀ k : Fin N, CtuParam ε hε (unitaryInvolution F 2 f) ι hι e k)
    (hagree : CtuParamAgree P) : SpGlobalCoverType e f κ := by
  obtain ⟨-, -, -, hqs, hodd, hLM⟩ := exists_ct_uniRow_of_agree hKc hf hN hF P hagree
  refine ⟨hqs, hodd, ?_⟩
  rcases hκ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hLM
  · exact hLM

end Recognition

end CFSG.SeitzReduction.SymplecticPilot
