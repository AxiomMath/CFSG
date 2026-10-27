module

public import CFSG.RankThree.PartOne.KE.E7FourHI
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E7FourAux.Core
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E7FourAux.PerX
public import CFSG.HardMathSupport.Solomon.LocalBalance.Balance
public import CFSG.HardMathSupport.Solomon.LocalBalance.Defs

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.LocalRank
open CFSG.RankThree.PartOne CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
open scoped Matrix Pointwise MatrixGroups

section HI

variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] {p : ℕ}
  {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]

theorem e7Four_card_map_comap_of_le_range {D C G : Type*} [Group D] [Group C] [Group G]
    (ι : D →* C) (hι : Function.Injective ι) (ψ : D →* G) (hψ : Function.Injective ψ)
    {P : Subgroup G} (hP : P ≤ ψ.range) : Nat.card ((P.comap ψ).map ι) = Nat.card P := by
  have hmap : (P.comap ψ).map ψ = P := by
    rw [Subgroup.map_comap_eq, inf_of_le_right hP]
  have e1 : (P.comap ψ) ≃* P := (Subgroup.equivMapOfInjective (P.comap ψ) ψ hψ).trans
    (MulEquiv.subgroupCongr hmap)
  have e2 : (P.comap ψ) ≃* (P.comap ψ).map ι := Subgroup.equivMapOfInjective _ ι hι
  exact Nat.card_congr (e1.symm.trans e2).symm.toEquiv

theorem e7_four_hI_pPrime (hD4 : D4TranspositionLayer Tag.E7) (F : E7FourFrame K L ℓ f p)
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + 1)
    (hstab : E7StabHyp F.n (iterateFrobenius L ℓ f) p)
    (hdiv : ∀ cert ∈ e7F4Certs, p ∣ Nat.card ↥(rootSpan .E7 L (e7D4Set cert) ⊓
      twistedFixedPoints F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))) :
    ∀ B : Subgroup (MulAut (adjointGroup .E7 K)),
      (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K)).range ≤ B →
      ∀ A : Subgroup (MulAut (adjointGroup .E7 K)), A ≤ B → IsElementaryAbelian p A →
        Nat.card A = p ^ 2 →
        A ≤ (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K)).range →
        localDeltaIn p B A = ⊥ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hΦ : ((Nat.card K : ℕ) : ZMod p) ^ 2 + 1 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((Nat.card K : ℤ) ^ 2 + 1) p).2 hpf
    simpa using this
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact iterateFrobenius_def ℓ f c
  intro B hB A hAB hA hcard hAin
  have hC : Subgroup.center (adjointGroup .E7 K) = ⊥ := center_adjointGroup_eq_bot
  have hIntinj : Function.Injective
      (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K)) :=
    conj_injective_of_center_eq_bot hC
  set A₀ : Subgroup (adjointGroup .E7 K) :=
    A.comap (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K)) with hA₀
  have hA₀map : A₀.map (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K)) = A := by
    rw [hA₀, Subgroup.map_comap_eq]
    exact inf_of_le_right hAin
  have hA₀card : Nat.card A₀ = p ^ 2 := by
    rw [← Subgroup.card_map_of_injective hIntinj, hA₀map, hcard]
  have hpg : IsPGroup p A₀ := IsPGroup.of_card hA₀card
  obtain ⟨c, hc⟩ := F.hconj A₀ hpg
  have hpow : ∀ a ∈ A, a ^ p = 1 := fun a ha =>
    elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) a ha
  have hA₀exp : ∀ q ∈ A₀, q ^ p = 1 := fun q hq => by
    apply hIntinj
    rw [map_pow, map_one]
    exact hpow _ hq
  let φ : A₀ →* ModGL .E7 L := (MulAut.conj F.g0⁻¹).toMonoidHom.comp
    ((adjEmb .E7 K L).comp ((MulAut.conj c).toMonoidHom.comp A₀.subtype))
  have hφ : ∀ q : A₀, φ q =
      F.g0⁻¹ * adjEmb .E7 K L (c * (q : adjointGroup .E7 K) * c⁻¹) * F.g0 := fun q => by
    simp [φ, MulAut.conj_apply]
  have hφinj : Function.Injective φ := by
    intro q q' h
    rw [hφ, hφ] at h
    have h1 := mul_left_cancel (mul_right_cancel h)
    have h2 := adjEmb_injective h1
    have h3 : (q : adjointGroup .E7 K) = q' := by
      have := congrArg (fun z => c⁻¹ * z * c) h2
      simpa [mul_assoc] using this
    exact Subtype.ext h3
  have hφT : ∀ q : A₀, φ q ∈ twistedTorusOf F.n (Units.map (entrywiseHom Fr)) := fun q => by
    rw [hφ]
    exact hc q q.2
  choose β hβ using fun q : A₀ =>
    (exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 (hφT q)).1 :
      ∃ b : Fin Tag.E7.rank → Lˣ, φ q = rootDiagUnit .E7 b)
  have hinj0 : Function.Injective (rootDiagUnitHom .E7 L) := rootDiagUnit_injective
  have hβmul : ∀ q q' : A₀, β (q * q') = β q * β q' := fun q q' => by
    apply rootDiagUnit_injective (τ := .E7) (K := L)
    rw [← hβ, rootDiagUnit_mul, ← hβ, ← hβ, map_mul]
  have hβone : β 1 = 1 := by
    apply rootDiagUnit_injective (τ := .E7) (K := L)
    rw [← hβ, map_one, rootDiagUnit_one]
  have hβfix : ∀ q : A₀, β q ∈ fixedCharTuples e7F4W Fr := fun q => by
    have h := hφT q
    rw [F.hT] at h
    obtain ⟨b, hb, hbq⟩ := h
    have : b = β q := hinj0 (hbq.trans (hβ q))
    rw [← this]
    exact hb
  have hβp : ∀ q : A₀, ∀ i, β q i ^ p = 1 := fun q i => by
    have h1 : rootDiagUnit .E7 (β q) ^ p = 1 := by
      rw [← hβ, ← map_pow]
      have : q ^ p = 1 := Subtype.ext (hA₀exp q q.2)
      rw [this, map_one]
    have h2 : β q ^ p = 1 := by
      apply hinj0
      rw [map_pow, map_one]
      exact h1
    exact congrFun h2 i
  have hβne : ∀ q : A₀, q ≠ 1 → β q ≠ 1 := fun q hq h => by
    apply hq
    apply hφinj
    rw [hβ, h, rootDiagUnit_one, map_one]
  have hsix : ∀ j : Fin 6, ∃ q : A₀, q ≠ 1 ∧ ∃ cert ∈ e7F4Certs, cert.cls = j.val ∧
      rootCharKernel (β q) = e7F4S0Set ∪ classSetL7 e7F4Rows j.val := by
    intro j
    set r : Fin Tag.E7.rank → ℤ := toVec Tag.E7.rank (e7F4ClassRoots.getD j.val []) with hrdef
    have hr : IsRoot .E7 r := isRoot_toVec (e7F4_classRoots_isRoot j.val j.2)
    let χ : A₀ →* Lˣ :=
      { toFun := fun q => rootChar (β q) r
        map_one' := by rw [hβone]; exact CTTorus.rootChar_one r
        map_mul' := fun q q' => by rw [hβmul, CTTorus.rootChar_mul] }
    have hχp : ∀ q : A₀, χ q ^ p = 1 := fun q => by
      rw [← map_pow]
      have h3 : q ^ p = 1 := Subtype.ext (hA₀exp q q.2)
      rw [h3, map_one]
    obtain ⟨q₀, hq₀1, hq₀χ⟩ := exists_ne_one_ker_of_card_sq hp hA₀card χ hχp
    refine ⟨q₀, hq₀1, ?_⟩
    have hrk : r ∈ rootCharKernel (β q₀) := ⟨hr, hq₀χ⟩
    rcases e7F4_kernel_structure Fr hFr hp hp3 hΦ (hβfix q₀) (hβp q₀) (hβne q₀ hq₀1) with
      hker | ⟨cert, hcert, hker, -⟩
    · exfalso
      rw [hker] at hrk
      obtain ⟨l, hl, hrl⟩ := hrk
      exact e7F4_classRoots_notS0' j.val j.2 l hl hrl
    · rw [hker] at hrk
      rcases hrk with ⟨l, hl, hrl⟩ | ⟨l, hl, hrl⟩
      · exact absurd hrl (e7F4_classRoots_notS0' j.val j.2 l hl)
      · have hjk : j.val = cert.cls := e7F4_classRoots_unique' j.val j.2 cert.cls
          (e7F4_certs_cls_lt cert hcert) l hl hrl
        exact ⟨cert, hcert, hjk.symm, by rw [hker, hjk]; rfl⟩
  choose xj hxj1 certj hcertj hclsj hkerj using hsix
  have hxjC : ∀ j, (xj j : adjointGroup .E7 K) ≠ 1 := fun j h => hxj1 j (Subtype.ext h)
  have hthetaT_le : ∀ a ∈ A, a ≠ 1 → localDeltaIn p B A ≤
      GLAPPrimeCoreOf p
        (B ⊓ Subgroup.centralizer ({a} : Set (MulAut (adjointGroup .E7 K)))) :=
    fun a ha ha1 => by
      refine iInf₂_le_of_le a ha ?_
      exact iInf_le_of_le ha1 le_rfl
  have hxjA : ∀ j, (MulAut.conj (xj j : adjointGroup .E7 K) : MulAut (adjointGroup .E7 K)) ∈ A :=
    fun j => (xj j).2
  have hne1 : ∀ j, (MulAut.conj (xj j : adjointGroup .E7 K) : MulAut (adjointGroup .E7 K)) ≠ 1 :=
    fun j h => hxjC j (hIntinj (h.trans (map_one _).symm))
  have hxjp : ∀ j, orderOf (xj j : adjointGroup .E7 K) = p := fun j =>
    orderOf_eq_prime (hA₀exp _ (xj j).2) (hxjC j)
  have hhj : ∀ j, F.g0⁻¹ * adjEmb .E7 K L (c * (xj j : adjointGroup .E7 K) * c⁻¹) * F.g0 ∈
      twistedTorusOf F.n (Units.map (entrywiseHom Fr)) := fun j => hc _ (xj j).2
  have hbhj : ∀ j, rootDiagUnit .E7 (β (xj j)) =
      F.g0⁻¹ * adjEmb .E7 K L (c * (xj j : adjointGroup .E7 K) * c⁻¹) * F.g0 := fun j => by
    rw [← hβ, hφ]
  have hdata := fun j : Fin 6 => e7_four_perx_special_def hD4 F hf hK hp hstab (hxjp j) c (hhj j)
    (hbhj j) (certj j) (hcertj j) (by rw [hclsj j]; exact hkerj j)
  choose ψ hψinj hψ hψHQ hψR hψadj PD hPD hPψ hPfin hPq hPnorm hcent hone hsub hsl using hdata
  have hdivj : ∀ j : Fin 6, p ∣ Nat.card ↥(PD j) := fun j => by
    rw [hPD j]
    exact hdiv (certj j) (hcertj j)
  have hbot : localDeltaIn p B A = ⊥ := by
    rw [eq_bot_iff]
    intro η hη
    have hηj : ∀ j, η ∈ GLAPPrimeCoreOf p
        (B ⊓ Subgroup.centralizer ({(MulAut.conj (xj j : adjointGroup .E7 K) :
          MulAut (adjointGroup .E7 K))} : Set (MulAut (adjointGroup .E7 K)))) :=
      fun j => hthetaT_le _ (hxjA j) (hne1 j) hη
    have hηM : ∀ j, η ∈ B ⊓ Subgroup.centralizer ({(MulAut.conj (xj j : adjointGroup .E7 K) :
        MulAut (adjointGroup .E7 K))} : Set (MulAut (adjointGroup .E7 K))) :=
      fun j => Subgroup.map_subtype_le _ (hηj j)
    have hfix : ∀ j : Fin 6, ∀ k ∈ ((PD j).comap (ψ j)).map
        (Subgroup.centralizer ({(xj j : adjointGroup .E7 K)} :
          Set (adjointGroup .E7 K))).subtype, η k = k := fun j =>
      core_pPrime_fixes_of_normal_quasisimple hp hC hB
        (isQuasisimple_map_comap_of_le_range _ (Subgroup.subtype_injective _) (ψ j) (hψinj j)
          (hPψ j) (hPq j))
        (by
          rw [e7Four_card_map_comap_of_le_range _ (Subgroup.subtype_injective _) (ψ j) (hψinj j) (hPψ j),
            hp.coprime_iff_not_dvd]
          exact not_not.2 (hdivj j))
        (Subgroup.map_subtype_le _)
        (fun d hd k hk => by
          obtain ⟨k', hk', rfl⟩ := hk
          refine ⟨⟨d, hd⟩ * k' * ⟨d, hd⟩⁻¹, ?_, rfl⟩
          show ψ j (⟨d, hd⟩ * k' * ⟨d, hd⟩⁻¹) ∈ PD j
          rw [map_mul, map_mul, map_inv]
          exact hPnorm j ⟨d, hd⟩ _ hk') η (hηj j)
    obtain ⟨h₀, hh₀⟩ := hsl 0 ⟨3, by decide⟩ rfl
    obtain ⟨g, a, hηu⟩ := e7_core_normalForm K L c F.g0 (ψ 0) (hψ 0) (hPψ 0) ⟨3, by decide⟩ h₀
      hh₀ η (hfix 0)
    set uK : ModGL .E7 K := (g : ModGL .E7 K) * rootDiagUnit .E7 a with huK
    have hcommu : ∀ y : adjointGroup .E7 K, η y = y →
        uK * (y : ModGL .E7 K) = (y : ModGL .E7 K) * uK := by
      intro y hy
      have h1 := hηu y
      rw [hy] at h1
      calc uK * (y : ModGL .E7 K) = (uK * (y : ModGL .E7 K) * uK⁻¹) * uK := by group
        _ = (y : ModGL .E7 K) * uK := by rw [← h1]
    set Y : ModGL .E7 L := e7Y F (c : ModGL .E7 K) uK with hY
    have hYmem : Y ∈ adjointGroup .E7 L := e7Y_mem F c.2 g.2 a
    have hYcomm : ∀ j, ∀ u ∈ PD j, Y * u = u * Y := by
      intro j u hu
      obtain ⟨k, hk⟩ := hPψ j hu
      have hkK : (k : adjointGroup .E7 K) ∈ ((PD j).comap (ψ j)).map
          (Subgroup.centralizer ({(xj j : adjointGroup .E7 K)} :
            Set (adjointGroup .E7 K))).subtype := ⟨k, by
        show ψ j k ∈ PD j
        rw [hk]
        exact hu, rfl⟩
      have h := e7Y_commute F c (k : adjointGroup .E7 K) uK
        (hcommu _ (hfix j (k : adjointGroup .E7 K) hkK))
      rw [← hψ j k, hk] at h
      exact h
    have hYHQ : ∀ j, Y ∈ torusGroup .E7 L ⊔ rootSpan .E7 L (rootCharKernel (β (xj j))) := by
      intro j
      have hηx : η (xj j : adjointGroup .E7 K) = (xj j : adjointGroup .E7 K) := by
        refine fixes_of_commute_conj hC η (xj j : adjointGroup .E7 K) ?_
        have h := Subgroup.mem_centralizer_iff.1 (hηM j).2 (MulAut.conj (xj j : adjointGroup .E7 K))
          rfl
        exact h.symm
      have hcx := e7Y_commute F c (xj j : adjointGroup .E7 K) uK (hcommu _ hηx)
      rw [← hbhj j] at hcx
      have hS : ∀ α ∈ rootCharKernel (β (xj j)), IsRoot .E7 α := fun α hα => hα.1
      have hSn : ∀ α ∈ rootCharKernel (β (xj j)), -α ∈ rootCharKernel (β (xj j)) := fun α hα =>
        ⟨IsRoot.neg hα.1, by rw [rootChar_neg', hα.2, inv_one]⟩
      have hstab' := hstab (β (xj j)) (hβp _) (hβne _ (hxj1 j)) (by rw [← hβ]; exact hφT _)
      have hmul := mem_torus_mul_rootSpan_of_commute_of_stab hstab' hS hSn (fun α hα => hα)
        hYmem hcx
      rwa [← Subgroup.coe_mul_of_left_le_normalizer_right _ _
        (KE.torusGroup_le_normalizer_rootSpan hS)] at hmul
    have hYcentD : ∀ j, Y ∈ Subgroup.centralizer
        (rootSpan .E7 L (e7D4Set (certj j)) : Set (ModGL .E7 L)) := fun j =>
      hcent j Y (hYHQ j) (hYcomm j)
    have hcover : ∀ α, IsRoot .E7 α → ∃ j : Fin 6, α ∈ e7D4Set (certj j) := by
      intro α hα
      obtain ⟨cert, hcert, hαc⟩ := e7F4_d4_cover_set hα
      have hlt : cert.cls < 6 := e7F4_certs_cls_lt cert hcert
      refine ⟨⟨cert.cls, hlt⟩, ?_⟩
      have hw := e7F4_certs_w_unique cert hcert (certj ⟨cert.cls, hlt⟩)
        (hcertj ⟨cert.cls, hlt⟩) (hclsj ⟨cert.cls, hlt⟩).symm
      unfold e7D4Set at hαc ⊢
      rw [hw] at hαc
      exact hαc
    have hYcent : ∀ α, IsRoot .E7 α → ∀ t : L, pinnedX .E7 L α t * Y = Y * pinnedX .E7 L α t := by
      intro α hα t
      obtain ⟨j, hj⟩ := hcover α hα
      exact Subgroup.mem_centralizer_iff.1 (hYcentD j) _ (pinnedX_mem_rootSpan hj t)
    have hYone : Y = 1 := by
      have hle : adjointGroup .E7 L ≤ Subgroup.centralizer ({Y} : Set (ModGL .E7 L)) := by
        refine (Subgroup.closure_le _).2 ?_
        rintro g ⟨i, t, hg⟩
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        rcases hg with hg | hg
        · have hgx : g = xUnit .E7 L i t := Units.ext hg
          rw [hgx, ← pinnedX_single]
          exact (hYcent (Pi.single i 1) (IsRoot.basis i) t).symm
        · have hgy : g = yUnit .E7 L i t := Units.ext hg
          rw [hgy, ← pinnedX_neg_single]
          exact (hYcent (-Pi.single i 1) (IsRoot.neg (IsRoot.basis i)) t).symm
      have hcen : (⟨Y, hYmem⟩ : adjointGroup .E7 L) ∈ Subgroup.center (adjointGroup .E7 L) := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (hle g.2) Y rfl).symm
      rw [center_adjointGroup_eq_bot_field .E7 L] at hcen
      exact congrArg Subtype.val (Subgroup.mem_bot.1 hcen)
    have hu1 : uK = 1 := e7Y_eq_one F (c : ModGL .E7 K) uK hYone
    have hη1 : η = 1 := by
      refine MulEquiv.ext fun y => Subtype.ext ?_
      rw [hηu y, hu1]
      simp
    rw [hη1]
    exact Subgroup.one_mem _
  exact hbot

end HI

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
