module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapN9A

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem five_le_of_isQuasisimple_alt {Q : Type*} [Group Q] {m : ℕ} (hm : Odd m)
    (hQ : IsQuasisimple Q) (e : Q ≃* alternatingGroup (Fin m)) : 5 ≤ m := by
  by_contra h
  have hm3 : m = 1 ∨ m = 3 := by
    obtain ⟨k, hk⟩ := hm
    omega
  obtain ⟨-, -, a, b, hab⟩ := hQ
  apply hab
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  apply e.injective
  rw [map_mul, map_mul]
  rcases hm3 with rfl | rfl
  · have h1 : Nat.card (alternatingGroup (Fin 1)) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨inferInstance, inferInstance⟩
    have : Subsingleton (alternatingGroup (Fin 1)) := (Nat.card_eq_one_iff_unique.mp h1).1
    exact Subsingleton.elim _ _
  · have h3 : Nat.card (alternatingGroup (Fin 3)) = 3 := by
      rw [nat_card_alternatingGroup, Nat.card_fin]
      rfl
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hc : IsCyclic (alternatingGroup (Fin 3)) := isCyclic_of_prime_card h3
    exact hc.isMulCommutative.is_comm.comm _ _

namespace SwapP2

@[expose] def ClaimAHolds (J : Subgroup X) (n : ℕ)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) (E : Subgroup X) : Prop :=
  ∀ F : Subgroup X, F ≤ J →
    Nonempty (F ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) →
  ∀ DF : Finset (Fin n), DF.card = 4 → (∀ x : J, (x : X) ∈ F → ∀ ω ∉ DF,
      ((e (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin n)) : Perm (Fin n)) ω = ω) →
  ∀ f ∈ F, f ≠ 1 → centralizer ({f} : Set X) ≤ Hn E

@[expose] def SwapMemberResidueNineExotic : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : X) (J : Subgroup X) (n : ℕ)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) (E : Subgroup X) (D : Finset (Fin n)),
    Sig36 X t J n e E D → n = 9 →
    centralizer ({t} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X) →
    ∀ M : Subgroup X, M ≤ normalizer (Sol78.signalizerCompletion E E : Set X) →
      IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))) →
      M.map (MulAut.conj t).toMonoidHom ≠ M → J ≤ M ⊔ M.map (MulAut.conj t).toMonoidHom →
      Nonempty (↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n)) →
      (∀ P : Subgroup X, P ≤ UnbalancedLayer.coreActionKernel J → IsPGroup 2 P →
        Nat.card P ≤ 2) →
      (∀ R : Subgroup X, R ≠ ⊥ → IsPGroup 2 R →
        R ≤ normalizer (Sol78.signalizerCompletion E E : Set X) →
        R ≤ UnbalancedLayer.coreActionKernel M →
        ¬ centralizer (R : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X)) →
      ClaimAHolds J n e E →
      (∃ (e₀ : X) (F : Subgroup X) (DF : Finset (Fin n)) (r : X) (N₁ : Subgroup X),
        Data t J n e E D M e₀ F DF r ∧ PumpData M e₀ r N₁ ∧ conjBy N₁ e₀ = N₁ ∧
          ∀ m : ℕ, Odd m → IsEmpty (↥N₁ ⧸ pPrimeCore 2 ↥N₁ ≃* alternatingGroup (Fin m))) →
      FooteLit.IsSolomonMember M

theorem isSolomonMember_of_pumpData_le [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X}
    {n : ℕ} {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X}
    {D : Finset (Fin n)} {M : Subgroup X} {e₀ : X} {F : Subgroup X} {DF : Finset (Fin n)}
    {r : X} {N₁ : Subgroup X} (hs : Setting t J n e E D M) (hd : Data t J n e E D M e₀ F DF r)
    (he₀H : centralizer ({e₀} : Set X) ≤ Hn E) (hP : PumpData M e₀ r N₁)
    (hfix : conjBy N₁ e₀ = N₁) (hN₁H : N₁ ≤ Hn E) : FooteLit.IsSolomonMember M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMr := fixedLayerComponent_holds X t J n e E D M hs e₀ F DF r hd he₀H N₁ hP hfix hN₁H
  have htH : t ∈ Hn E := hs.cent (mem_centralizer_singleton_iff.mpr rfl)
  obtain ⟨hMtH, hMtpc⟩ := isPComponent_conj hs.le hs.pc htH
  have hMtK : conjBy M t ≤ UnbalancedLayer.coreActionKernel M :=
    GSThmB.B5a.le_coreActionKernel_of_ne hs.le hMtH hs.pc hMtpc (Ne.symm hs.swap)
  have hr2 : orderOf r = 2 := orderOf_eq_prime (by rw [sq]; exact hd.r2) hd.r1
  have hR2 : IsPGroup 2 (zpowers r) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hr2, pow_one])
  obtain ⟨-, -, hMq⟩ :=
    (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 M (Hn E) hs.le).mp hs.pc
  have hperf : ⁅M, M⁆ = M := UnbalancedCorr.commutator_eq_of_isPComponent hs.le hs.pc
  refine memberOfFixedLayer_holds X M (zpowers r) hperf hMq
    (fun h => hd.r1 (zpowers_eq_bot.mp h)) hR2 (zpowers_le.mpr (hMtK hd.rM)) ?_
  rwa [centralizer_zpowers_eq' r]

theorem degree_le_of_pumpData [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
    {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
    {M : Subgroup X} {e₀ : X} {F : Subgroup X} {DF : Finset (Fin n)} {r : X}
    {N₁ : Subgroup X} (hs : Setting t J n e E D M) (hd : Data t J n e E D M e₀ F DF r)
    (hP : PumpData M e₀ r N₁) {m : ℕ} (hmo : Odd m)
    (θN : ↥N₁ ⧸ pPrimeCore 2 ↥N₁ ≃* alternatingGroup (Fin m)) : 5 ≤ m ∧ m ≤ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hNq⟩ :=
    (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 N₁ _ hP.le).mp hP.pc
  have hr2 : orderOf r = 2 := orderOf_eq_prime (by rw [sq]; exact hd.r2) hd.r1
  exact ⟨five_le_of_isQuasisimple_alt hmo hNq θN,
    hs.sig.pair.2.2.2.1 r N₁ m ⟨hr2, hP.le, hP.pc, ⟨θN⟩⟩ hmo⟩

theorem nonempty_fusionZStar_of_diagonal [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X}
    {n : ℕ} {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X}
    {D : Finset (Fin n)} {M : Subgroup X} {e₀ : X} {F : Subgroup X} {DF : Finset (Fin n)}
    {r : X} {N₁ : Subgroup X} (hs : Setting t J n e E D M) (hd : Data t J n e E D M e₀ F DF r)
    (he₀H : centralizer ({e₀} : Set X) ≤ Hn E) (hP : PumpData M e₀ r N₁)
    (hdiag : conjBy N₁ e₀ ≠ N₁) :
    Nonempty (↥N₁ ⧸ Open.fusionZStar ↥N₁ ≃* alternatingGroup (Fin (n - 4))) := by
  have hn9 := hs.sig.nine_le
  obtain ⟨⟨χr⟩, ⟨hArle, -⟩, -⟩ := pump_holds X t J n e E D M hs e₀ F DF r hd he₀H
  have he₀2 : e₀ * e₀ = 1 := by rw [← sq]; exact (card_sq_of_klein hs.sig.klein).2 e₀ hd.e₀E
  have he₀o : orderOf e₀ = 2 := orderOf_eq_prime (by rw [sq]; exact he₀2) hd.e₀1
  have he₀r : e₀ ∈ centralizer ({r} : Set X) := mem_centralizer_singleton_iff.mpr hd.re₀.symm
  obtain ⟨φ⟩ := swap_type_in (M := N₁) he₀r he₀o hP.le hP.pc hdiag hP.cover
    (hArle.trans inf_le_right) hP.layer
  have hZ : Open.fusionZStar ↥(fixA M e₀ r) = pPrimeCore 2 ↥(fixA M e₀ r) :=
    fusionZStar_eq_of_alt (by omega) χr
  exact ⟨φ.symm.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans χr)⟩

@[expose] def SwapMemberResidueNineExoticT2 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : X) (J : Subgroup X) (n : ℕ)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) (E : Subgroup X) (D : Finset (Fin n)),
    Sig36 X t J n e E D → n = 9 →
    centralizer ({t} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X) →
    ∀ M : Subgroup X, M ≤ normalizer (Sol78.signalizerCompletion E E : Set X) →
      IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))) →
      M.map (MulAut.conj t).toMonoidHom ≠ M → J ≤ M ⊔ M.map (MulAut.conj t).toMonoidHom →
      Nonempty (↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n)) →
      (∀ P : Subgroup X, P ≤ UnbalancedLayer.coreActionKernel J → IsPGroup 2 P →
        Nat.card P ≤ 2) →
      (∀ R : Subgroup X, R ≠ ⊥ → IsPGroup 2 R →
        R ≤ normalizer (Sol78.signalizerCompletion E E : Set X) →
        R ≤ UnbalancedLayer.coreActionKernel M →
        ¬ centralizer (R : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X)) →
      ClaimAHolds J n e E →
      (∃ (e₀ : X) (F : Subgroup X) (DF : Finset (Fin n)) (r : X) (N₁ : Subgroup X),
        Data t J n e E D M e₀ F DF r ∧ PumpData M e₀ r N₁ ∧ conjBy N₁ e₀ = N₁ ∧
          (∀ m : ℕ, Odd m → IsEmpty (↥N₁ ⧸ pPrimeCore 2 ↥N₁ ≃* alternatingGroup (Fin m))) ∧
          ¬ fixB M t e₀ r ≤ N₁) →
      FooteLit.IsSolomonMember M

@[expose] def SwapMemberResidueNineExoticT3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : X) (J : Subgroup X) (n : ℕ)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) (E : Subgroup X) (D : Finset (Fin n)),
    Sig36 X t J n e E D → n = 9 →
    centralizer ({t} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X) →
    ∀ M : Subgroup X, M ≤ normalizer (Sol78.signalizerCompletion E E : Set X) →
      IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))) →
      M.map (MulAut.conj t).toMonoidHom ≠ M → J ≤ M ⊔ M.map (MulAut.conj t).toMonoidHom →
      Nonempty (↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n)) →
      (∀ P : Subgroup X, P ≤ UnbalancedLayer.coreActionKernel J → IsPGroup 2 P →
        Nat.card P ≤ 2) →
      (∀ R : Subgroup X, R ≠ ⊥ → IsPGroup 2 R →
        R ≤ normalizer (Sol78.signalizerCompletion E E : Set X) →
        R ≤ UnbalancedLayer.coreActionKernel M →
        ¬ centralizer (R : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X)) →
      ClaimAHolds J n e E →
      (∃ (e₀ : X) (F : Subgroup X) (DF : Finset (Fin n)) (r : X) (N₁ : Subgroup X),
        Data t J n e E D M e₀ F DF r ∧ PumpData M e₀ r N₁ ∧ conjBy N₁ e₀ = N₁ ∧
          (∀ m : ℕ, Odd m → IsEmpty (↥N₁ ⧸ pPrimeCore 2 ↥N₁ ≃* alternatingGroup (Fin m))) ∧
          fixB M t e₀ r ≤ N₁) →
      FooteLit.IsSolomonMember M

theorem swapMemberResidueNineExotic_of_split (h2 : SwapMemberResidueNineExoticT2)
    (h3 : SwapMemberResidueNineExoticT3) : SwapMemberResidueNineExotic := by
  intro X _ _ _ t J n e E D S hn hCH M hMH hMpc hne hJM hMalt hsmall hnarrow hCA hex
  obtain ⟨e₀, F, DF, r, N₁, hd, hP, hfix, hexo⟩ := hex
  by_cases hB : fixB M t e₀ r ≤ N₁
  · exact h3 X t J n e E D S hn hCH M hMH hMpc hne hJM hMalt hsmall hnarrow hCA
      ⟨e₀, F, DF, r, N₁, hd, hP, hfix, hexo, hB⟩
  · exact h2 X t J n e E D S hn hCH M hMH hMpc hne hJM hMalt hsmall hnarrow hCA
      ⟨e₀, F, DF, r, N₁, hd, hP, hfix, hexo, hB⟩

@[expose] def PumpSideNine : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : X) (J : Subgroup X) (n : ℕ)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) (E : Subgroup X) (D : Finset (Fin n))
    (M : Subgroup X), Setting t J n e E D M → n = 9 →
    ∀ (e₀ : X) (F : Subgroup X) (DF : Finset (Fin n)) (r : X), Data t J n e E D M e₀ F DF r →
    centralizer ({e₀} : Set X) ≤ Hn E →
    ∀ N₁ : Subgroup X, PumpData M e₀ r N₁ → conjBy N₁ e₀ = N₁ →
    ∀ m : ℕ, Odd m → Nonempty (↥N₁ ⧸ pPrimeCore 2 ↥N₁ ≃* alternatingGroup (Fin m)) →
    ∀ f ∈ F, ∃ a ∈ fixA M e₀ r, f * a⁻¹ ∈ UnbalancedLayer.coreActionKernel N₁ ∧
      f * a⁻¹ ∈ UnbalancedLayer.coreActionKernel M

@[expose] def PumpDiagNine : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : X) (J : Subgroup X) (n : ℕ)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) (E : Subgroup X) (D : Finset (Fin n))
    (M : Subgroup X), Setting t J n e E D M → n = 9 →
    ∀ (e₀ : X) (F : Subgroup X) (DF : Finset (Fin n)) (r : X), Data t J n e E D M e₀ F DF r →
    centralizer ({e₀} : Set X) ≤ Hn E →
    core (centralizer ({r} : Set X)) ≤ Hn E →
    (∀ f ∈ F, f ≠ 1 → centralizer ({f} : Set X) ≤ Hn E) →
    ∀ N₁ : Subgroup X, PumpData M e₀ r N₁ → conjBy N₁ e₀ = N₁

theorem isSolomonMember_nine (hPS : PumpSideNine) (hPD : PumpDiagNine)
    (hEx : SwapMemberResidueNineExotic) [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X}
    {n : ℕ} {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X}
    {D : Finset (Fin n)} {M : Subgroup X} (hs : Setting t J n e E D M) (hn : n = 9)
    (hCA : ClaimAHolds J n e E) : FooteLit.IsSolomonMember M := by
  classical
  have S := hs.sig
  obtain ⟨e₀, -, -, he₀E, -, -, he₀1, -, -, -, -, -⟩ := exists_three_of_klein S.klein
  obtain ⟨F, DF, r, hd⟩ := dataExist_holds X t J n e E D M hs e₀ he₀E he₀1
  have hFH := hCA F hd.FJ hd.Fk DF hd.DFc hd.Fs
  have he₀H : centralizer ({e₀} : Set X) ≤ Hn E :=
    hCA E S.le S.klein D S.card S.supp e₀ he₀E he₀1
  have hOr := oddCoreR_holds X t J n e E D M hs e₀ F DF r hd hFH
  obtain ⟨-, -, N₁, hN₁⟩ := pump_holds X t J n e E D M hs e₀ F DF r hd he₀H
  have hfix := hPD X t J n e E D M hs hn e₀ F DF r hd he₀H hOr hFH N₁ hN₁
  by_cases hA : ∃ m : ℕ, Odd m ∧ Nonempty (↥N₁ ⧸ pPrimeCore 2 ↥N₁ ≃* alternatingGroup (Fin m))
  · obtain ⟨m, hmo, ⟨θN⟩⟩ := hA
    have hside := hPS X t J n e E D M hs hn e₀ F DF r hd he₀H N₁ hN₁ hfix m hmo ⟨θN⟩
    obtain ⟨hm5, -⟩ := degree_le_of_pumpData hs hd hN₁ hmo θN
    have hN₁H := le_of_exact' hs hd hOr hFH hN₁ hfix hside hmo (by omega) θN
    exact isSolomonMember_of_pumpData_le hs hd he₀H hN₁ hfix hN₁H
  · push Not at hA
    exact hEx X t J n e E D S hn hs.cent M hs.le hs.pc hs.swap hs.diag hs.alt hs.small
      hs.narrow hCA ⟨e₀, F, DF, r, N₁, hd, hN₁, hfix, fun m hm => hA m hm⟩

theorem swapMemberResidueNine_of_claimA (hPS : PumpSideNine) (hPD : PumpDiagNine)
    (hEx : SwapMemberResidueNineExotic) {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {t : X} {J : Subgroup X} {n : ℕ} {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)}
    {E : Subgroup X} {D : Finset (Fin n)} (S : Sig36 X t J n e E D) (hn : n = 9)
    (hCH : centralizer ({t} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    {M : Subgroup X} (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hne : M.map (MulAut.conj t).toMonoidHom ≠ M) (hJM : J ≤ M ⊔ M.map (MulAut.conj t).toMonoidHom)
    (hMalt : Nonempty (↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n)))
    (hsmall : ∀ P : Subgroup X, P ≤ UnbalancedLayer.coreActionKernel J → IsPGroup 2 P →
      Nat.card P ≤ 2)
    (hnarrow : ∀ R : Subgroup X, R ≠ ⊥ → IsPGroup 2 R →
      R ≤ normalizer (Sol78.signalizerCompletion E E : Set X) →
      R ≤ UnbalancedLayer.coreActionKernel M →
      ¬ centralizer (R : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hCA : ClaimAHolds J n e E) : FooteLit.IsSolomonMember M :=
  isSolomonMember_nine hPS hPD hEx ⟨S, hCH, hMH, hMpc, hne, hJM, hMalt, hsmall, hnarrow⟩ hn hCA

end SwapP2

end CFSG.ComponentClassification.SolMax
