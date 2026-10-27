module

public import CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport.FamilyReduction
public import CFSG.HardMathSupport.Seitz.Proving.CentralizerPairTransport
public import CFSG.Blueprint.Catalog

public section

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport

namespace CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator

variable {G : Type*} [Group G]

@[expose] def CentralizerPairGenerationSylow (G : Type*) [Group G] (p : ℕ) : Prop :=
  ∀ P : Sylow p G, ∀ z ∈ P, (∀ x ∈ P, x * z = z * x) → z ≠ 1 → z ^ p = 1 →
    ∀ e ∈ P, e ≠ 1 → e ^ p = 1 → e ∉ Subgroup.zpowers z →
      Subgroup.centralizer {z} ⊔ Subgroup.centralizer {e} = ⊤

theorem CentralizerPairGenerationSylow.of_mulEquiv {H : Type*} [Group H] {p : ℕ} (φ : G ≃* H)
    (h : CentralizerPairGenerationSylow G p) : CentralizerPairGenerationSylow H p := by
  intro P z hzP hzc hz1 hzp e heP he1 hep hez
  have hrange : (P : Subgroup H) ≤ φ.toMonoidHom.range := fun x _ =>
    ⟨φ.symm x, by simp⟩
  set Q : Sylow p G := P.comapOfInjective φ.toMonoidHom φ.injective hrange with hQ
  have hmemQ : ∀ y : G, y ∈ Q ↔ φ y ∈ P := fun y => Iff.rfl
  have hzQ : φ.symm z ∈ Q := by rw [hmemQ, MulEquiv.apply_symm_apply]; exact hzP
  have heQ : φ.symm e ∈ Q := by rw [hmemQ, MulEquiv.apply_symm_apply]; exact heP
  have hzcQ : ∀ x ∈ Q, x * φ.symm z = φ.symm z * x := by
    intro x hx
    apply φ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hzc (φ x) ((hmemQ x).1 hx)
  have hz1' : φ.symm z ≠ 1 := fun h1 => hz1 (by simpa using congrArg φ h1)
  have he1' : φ.symm e ≠ 1 := fun h1 => he1 (by simpa using congrArg φ h1)
  have hzp' : φ.symm z ^ p = 1 := by rw [← map_pow, hzp, map_one]
  have hep' : φ.symm e ^ p = 1 := by rw [← map_pow, hep, map_one]
  have hez' : φ.symm e ∉ Subgroup.zpowers (φ.symm z) := by
    rintro ⟨k, hk⟩
    apply hez
    refine ⟨k, ?_⟩
    have := congrArg φ hk
    simpa [map_zpow] using this
  have htop := h Q _ hzQ hzcQ hz1' hzp' _ heQ he1' hep' hez'
  have hmap := congrArg (Subgroup.map φ.toMonoidHom) htop
  rw [Subgroup.map_sup, CFSG.HardMathSupport.Seitz.Proving.map_centralizer_singleton,
    CFSG.HardMathSupport.Seitz.Proving.map_centralizer_singleton, MulEquiv.apply_symm_apply,
    MulEquiv.apply_symm_apply, Subgroup.map_top_of_surjective _ φ.surjective] at hmap
  exact hmap

theorem exists_sylow_central_in_plane [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (hrank : RankLE2 p G) {F : Subgroup G} (hF : IsElemAbelian p F) (hcard : Nat.card F = p ^ 2) :
    ∃ P : Sylow p G, F ≤ P ∧ ∃ z ∈ F, z ≠ 1 ∧ z ^ p = 1 ∧ ∀ x ∈ P, x * z = z * x := by
  classical
  obtain ⟨P, hFP⟩ := (isPGroup_of_pow_eq_one hF.2).exists_le_sylow
  have hPp : IsPGroup p (P : Subgroup G) := P.isPGroup'
  have hPnt : Nontrivial (P : Subgroup G) := by
    have hle : Nat.card F ≤ Nat.card (P : Subgroup G) := Subgroup.card_le_of_le hFP
    have h1 : 1 < Nat.card (P : Subgroup G) := by
      have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.out.one_lt
      omega
    exact Finite.one_lt_card_iff_nontrivial.1 h1
  have := hPp.center_nontrivial
  have hZp : IsPGroup p (Subgroup.center (P : Subgroup G)) := hPp.to_subgroup _
  obtain ⟨n, hn, hnc⟩ := (hZp.nontrivial_iff_card).1 inferInstance
  have hdvd : p ∣ Nat.card (Subgroup.center (P : Subgroup G)) := by
    rw [hnc]; exact dvd_pow_self p hn.ne'
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center (P : Subgroup G)) p hdvd
  set w : G := (((x : Subgroup.center (P : Subgroup G)) : (P : Subgroup G)) : G) with hw
  have hwp : w ^ p = 1 := by
    have : x ^ p = 1 := (orderOf_dvd_iff_pow_eq_one.1 hx.dvd)
    have := congrArg (fun y : Subgroup.center (P : Subgroup G) => (((y : (P : Subgroup G))) : G))
      this
    simpa [hw] using this
  have hw1 : w ≠ 1 := by
    intro h
    have : x = 1 := by
      apply Subtype.ext; apply Subtype.ext; simpa [hw] using h
    rw [this, orderOf_one] at hx
    exact hp.out.one_lt.ne hx
  have hwc : ∀ y ∈ P, y * w = w * y := by
    intro y hy
    have := Subgroup.mem_center_iff.1 x.2 ⟨y, hy⟩
    exact congrArg (fun t : (P : Subgroup G) => (t : G)) this
  have hwF : w ∈ F := by
    set F' := Subgroup.closure ((F : Set G) ∪ {w}) with hF'
    have hF'ab : IsElemAbelian p F' := by
      refine isElemAbelian_closure ?_ ?_
      · rintro a (ha | ha) b (hb | hb)
        · exact hF.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩ |> congrArg Subtype.val
        · rw [Set.mem_singleton_iff] at hb; subst hb; exact hwc a (hFP ha)
        · rw [Set.mem_singleton_iff] at ha; subst ha; exact (hwc b (hFP hb)).symm
        · rw [Set.mem_singleton_iff] at ha hb; subst ha; subst hb; rfl
      · rintro a (ha | ha)
        · exact hF.2 a ha
        · rw [Set.mem_singleton_iff] at ha; subst ha; exact hwp
    have hFF' : F ≤ F' := fun a ha => Subgroup.subset_closure (Or.inl ha)
    have hle : Nat.card F' ≤ Nat.card F := by rw [hcard]; exact hrank F' hF'ab
    have heq : F = F' := Subgroup.eq_of_le_of_card_ge hFF' hle
    have : w ∈ F' := Subgroup.subset_closure (Or.inr rfl)
    rwa [← heq] at this
  exact ⟨P, hFP, w, hwF, hw1, hwp, hwc⟩

theorem planeGen_of_pairGenerationSylow [Finite G] (hZ : Subgroup.center G = ⊥) {p : ℕ}
    [hp : Fact p.Prime] (hrank : RankLE2 p G) (hgen : CentralizerPairGenerationSylow G p)
    (E : Subgroup (MulAut G)) (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 2)
    (hin : E ≤ (MulAut.conj : G →* MulAut G).range) : PlaneGen E := by
  classical
  have hinj := conj_injective_of_center_eq_bot hZ
  set F : Subgroup G := E.comap (MulAut.conj : G →* MulAut G) with hFdef
  have hFE : F.map (MulAut.conj : G →* MulAut G) = E := Subgroup.map_comap_eq_self hin
  have hFcard : Nat.card F = p ^ 2 := by
    have := Subgroup.card_map_of_injective hinj (K := F)
    rw [hFE] at this
    exact this.symm.trans hcard
  have hFab : IsElemAbelian p F := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      apply hinj
      have h := congrArg Subtype.val
        (hE.1.is_comm.comm (⟨MulAut.conj (a : G), a.2⟩ : E) ⟨MulAut.conj (b : G), b.2⟩)
      simpa using h
    · apply hinj
      have := hE.2 _ hx
      simpa [map_pow] using this
  obtain ⟨P, hFP, z, hzF, hz1, hzp, hzc⟩ := exists_sylow_central_in_plane hrank hFab hFcard
  have hex : ∃ e ∈ F, e ∉ Subgroup.zpowers z := by
    by_contra h
    push Not at h
    have hle : F ≤ Subgroup.zpowers z := h
    have h1 : Nat.card F ≤ Nat.card (Subgroup.zpowers z) := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers] at h1
    have h2 : orderOf z ≤ p := Nat.le_of_dvd hp.out.pos (orderOf_dvd_of_pow_eq_one hzp)
    have h3 : p ^ 2 ≤ p := hFcard ▸ h1.trans h2
    have : p < p ^ 2 := by nlinarith [hp.out.one_lt]
    omega
  obtain ⟨e, heF, hez⟩ := hex
  have he1 : e ≠ 1 := fun h => hez (h ▸ one_mem _)
  have hep : e ^ p = 1 := hFab.2 e heF
  have htop := hgen P z (hFP hzF) hzc hz1 hzp e (hFP heF) he1 hep hez
  unfold PlaneGen
  rw [eq_top_iff, ← htop]
  have hz1' : (MulAut.conj z : MulAut G) ≠ 1 := fun h => hz1 (hinj (by rw [h, map_one]))
  have he1' : (MulAut.conj e : MulAut G) ≠ 1 := fun h => he1 (hinj (by rw [h, map_one]))
  rw [← hFE]
  apply sup_le
  · intro k hk
    rw [Subgroup.mem_centralizer_iff] at hk
    exact mem_planeClosure_of_commute hzF hz1' (hk z rfl).symm
  · intro k hk
    rw [Subgroup.mem_centralizer_iff] at hk
    exact mem_planeClosure_of_commute heF he1' (hk e rfl).symm

@[expose] def G2ThreeCentralizerPairsSylow : Prop :=
  ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.G2 q).Valid), 3 ∣ q.card + 1 →
    CentralizerPairGenerationSylow (Cat ⟨TauCeti.LieTypeIndex.G2 q, hv⟩) 3

theorem seitzExcAnisotropicG2ThreePlus_of_sylow (hb : G2ThreeCatBasic)
    (hg : G2ThreeCentralizerPairsSylow) : SeitzExcAnisotropicG2ThreePlus := by
  rintro d p hp hp2 hpd hex E hE hc ⟨⟨hin, -, hrank, -⟩, hp3, q, hdq, h3⟩
  obtain ⟨d1, hv⟩ := d
  obtain rfl : d1 = TauCeti.LieTypeIndex.G2 q := hdq
  subst hp3
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨hfin, hcen⟩ := hb q hv h3
  exact planeGen_of_pairGenerationSylow hcen hrank (hg q hv h3) E hE hc hin

@[expose] def G2NativeCentralizerPairsSylow : Prop :=
  ∀ (K : Type) [Field K] [Finite K], 3 ≤ Nat.card K → 3 ∣ Nat.card K + 1 →
    CentralizerPairGenerationSylow (adjointGroup .G2 K) 3

theorem g2ThreeCentralizerPairsSylow_of_native
    (hB : ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.G2 q).Valid)
      (K : Type) [Field K] [Finite K], Nat.card K = q.card →
        Nonempty (AdjointQuotient .G2 K ≃*
          TauCeti.ValidLieTypeIndex.Group ⟨TauCeti.LieTypeIndex.G2 q, hv⟩))
    (hcen : ∀ (K : Type) [Field K] [Finite K], Subgroup.center (adjointGroup .G2 K) = ⊥)
    (hN : G2NativeCentralizerPairsSylow) : G2ThreeCentralizerPairsSylow := by
  intro q hv h3
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  let K := GaloisField q.p q.exponent
  have hK : Nat.card K = q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact GaloisField.card q.p q.exponent q.exponent_pos.ne'
  obtain ⟨e⟩ := hB q hv K hK
  have e' : AdjointQuotient .G2 K ≃* ↥(adjointGroup .G2 K) :=
    (QuotientGroup.quotientMulEquivOfEq (hcen K)).trans QuotientGroup.quotientBot
  have hq3 : 3 ≤ q.card :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  exact CentralizerPairGenerationSylow.of_mulEquiv (e'.symm.trans e)
    (hN K (by rw [hK]; exact hq3) (by rw [hK]; exact h3))

end CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator
