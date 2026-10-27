module

public import CFSG.LocalAnalysis.ComponentClassification.FiveCatReduce
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatAltCover

public section

namespace CFSG.ComponentClassification.SolMax.FiveCat

open CFSG Subgroup CatLeaf Equiv CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

private theorem card_of_mulEquiv_alt_five {X : Type*} [Group X]
    (e : X ≃* alternatingGroup (Fin 5)) : Nat.card X = 60 := by
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem exists_equiv_alt_of_fixed_component {H : Type} [Group H] [Finite H] {M : Subgroup H}
    (hMq : IsQuasisimple (↥M ⧸ pPrimeCore 2 ↥M)) {T : Subgroup H} (hTM : T ≤ M)
    (eT : ↥T ⧸ pPrimeCore 2 ↥T ≃* alternatingGroup (Fin 5))
    {σ : MulAut ((↥M ⧸ pPrimeCore 2 ↥M) ⧸ center (↥M ⧸ pPrimeCore 2 ↥M))}
    (hP : ProperFixedComponent σ (imageInSimple M T))
    (eP : ↥(imageInSimple M T) ⧸ Open.fusionZStar ↥(imageInSimple M T) ≃*
      alternatingGroup (Fin 5))
    {m : ℕ} (hm7 : 7 ≤ m)
    (eS : (↥M ⧸ pPrimeCore 2 ↥M) ⧸ center (↥M ⧸ pPrimeCore 2 ↥M) ≃* alternatingGroup (Fin m)) :
    Nonempty (↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin m)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hP60, u, huP, p, q, s, t, hpq, hps, hpt, hqs, hqt, hst, hu⟩ :=
    altCover_exists_double_transposition (by omega) (by omega) eS hP eP
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  set G := ↥M ⧸ pPrimeCore 2 ↥M with hG
  set π : ↥M →* G := QuotientGroup.mk' (pPrimeCore 2 ↥M) with hπ
  set π₂ : G →* G ⧸ center G := QuotientGroup.mk' (center G) with hπ₂
  set T' : Subgroup M := T.subgroupOf M with hT'
  set P := imageInSimple M T with hPdef
  let ψ : ↥T' →* ↥P := ((π₂.comp π).comp T'.subtype).codRestrict P fun a =>
    ⟨π a, ⟨a, a.2, rfl⟩, rfl⟩
  have hψ : ∀ a : ↥T', ((ψ a : ↥P) : G ⧸ center G) = π₂ (π (a : M)) := fun a => rfl
  have hψs : Function.Surjective ψ := by
    rintro ⟨_, y, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩
  have eT' : ↥T' ⧸ pPrimeCore 2 ↥T' ≃* alternatingGroup (Fin 5) :=
    (Sol78.coreQuotCongr (subgroupOfEquivOfLe hTM)).trans eT
  have hc1 : Nat.card ↥T' = Nat.card ↥ψ.ker * Nat.card ↥P := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψs).toEquiv, mul_comm]
  have hc2 : Nat.card ↥T' = Nat.card ↥(pPrimeCore 2 ↥T') * 60 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥T'),
      card_of_mulEquiv_alt_five eT']
    rw [mul_comm]
  have hkodd : Odd (Nat.card ↥ψ.ker) := by
    have h : Nat.card ↥ψ.ker = Nat.card ↥(pPrimeCore 2 ↥T') := by
      rw [hP60] at hc1
      have h60 : 0 < 60 := by norm_num
      exact Nat.eq_of_mul_eq_mul_right h60 (by rw [← hc1, hc2])
    rw [h]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have huu : u * u = 1 := by
    apply eS.injective
    apply Subtype.ext
    rw [map_mul, map_one]
    change ((eS u : alternatingGroup (Fin (m' + 2))) : Perm (Fin (m' + 2))) *
      ((eS u : alternatingGroup (Fin (m' + 2))) : Perm (Fin (m' + 2))) = 1
    rw [hu, ← sq]
    exact swap_mul_swap_sq_of_ne hps hpt hqs.symm hqt
  obtain ⟨y, hyT, hyu⟩ := Subgroup.mem_map.mp huP
  obtain ⟨a, haT, hay⟩ := Subgroup.mem_map.mp hyT
  set a' : ↥T' := ⟨a, haT⟩ with ha'
  have hψa : ((ψ a' : ↥P) : G ⧸ center G) = u := by
    rw [hψ]
    change π₂ (π a) = u
    rw [hay, hyu]
  obtain ⟨j, hj⟩ := hkodd
  set a'' : ↥T' := a' ^ Nat.card ↥ψ.ker with ha''
  have hψa'' : ((ψ a'' : ↥P) : G ⧸ center G) = u := by
    rw [ha'', map_pow, Subgroup.coe_pow, hψa, hj, pow_succ, pow_mul, sq, huu, one_pow, one_mul]
  have ha''2 : a'' * a'' = 1 := by
    have hk : a' ^ 2 ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      change ((ψ (a' ^ 2) : ↥P) : G ⧸ center G) = 1
      rw [map_pow, Subgroup.coe_pow, hψa, sq, huu]
    have := pow_card_eq_one' (G := ↥ψ.ker) (x := ⟨a' ^ 2, hk⟩)
    have h2 : (a' ^ 2) ^ Nat.card ↥ψ.ker = 1 := congrArg (fun z : ↥ψ.ker => ((z : ↥T') : ↥T')) this
    rw [ha'', ← sq, ← pow_mul, mul_comm, pow_mul, h2]
  set g : G := π ((a'' : ↥T') : M) with hgdef
  have hgg : g * g = 1 := by
    have : ((a'' * a'' : ↥T') : M) = 1 := by rw [ha''2]; rfl
    rw [hgdef, ← map_mul]
    have h2 : (((a'' : ↥T') : M) * ((a'' : ↥T') : M)) = 1 := this
    rw [h2, map_one]
  let η : G →* alternatingGroup (Fin (m' + 2)) := eS.toMonoidHom.comp π₂
  have hηs : Function.Surjective η := eS.surjective.comp (QuotientGroup.mk'_surjective _)
  have hηker : η.ker = center G := by
    ext x
    rw [MonoidHom.mem_ker]
    change eS (π₂ x) = 1 ↔ _
    rw [map_eq_one_iff _ eS.injective, hπ₂, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hηK : η.ker ≤ center G := hηker.le
  have hηK2 : IsPGroup 2 η.ker := by
    rw [hηker]
    exact Sol78.center_isPGroup_two (pPrimeCore_quotient_pPrimeCore_eq_bot 2)
  haveI : Group.IsPerfect G := hMq.1
  have hηg : η g = eS u := by
    have h1 : π₂ (π ((a'' : ↥T') : M)) = u := (hψ a'').symm.trans hψa''
    change eS (π₂ (π ((a'' : ↥T') : M))) = eS u
    rw [h1]
  have hgη : ((η g : alternatingGroup (Fin (m' + 2))) : Perm (Fin (m' + 2))) =
      swap p q * swap s t := by
    rw [hηg, hu]
  have hker := altCover_ker_eq_bot_of_involution_lift (by omega) η hηs hηK hηK2 hpq hps hpt hqs hqt
    hst hgg hgη
  exact ⟨MulEquiv.ofBijective η ⟨(MonoidHom.ker_eq_bot_iff η).mp hker, hηs⟩⟩


private theorem FivePumpNonAlt.of_mulEquiv {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    (h : FivePumpNonAlt S) : FivePumpNonAlt S' := by
  unfold FivePumpNonAlt at h ⊢
  rcases h with h | h | h | h | h | h | h | h | h | h
  · exact Or.inl (Blueprint.LieModel.of_mulEquiv e h)
  · exact Or.inr (Or.inl (Blueprint.LieModel.of_mulEquiv e h))
  · exact Or.inr (Or.inr (Or.inl (Blueprint.LieModel.of_mulEquiv e h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Blueprint.LieModel.of_mulEquiv e h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Blueprint.LieModel.of_mulEquiv e h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Blueprint.LieModel.of_mulEquiv e h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl (Blueprint.LieModel.of_mulEquiv e h)))))))
  · obtain ⟨e'⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e.symm.trans e'⟩)))))))
  · obtain ⟨e'⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨e.symm.trans e'⟩))))))))
  · obtain ⟨e'⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr ⟨e.symm.trans e'⟩))))))))

theorem fivePumpUpInput_of_leaf (hleaf : FivePumpLeaf) : FivePumpUpInput := by
  intro H _ _ hK M hM x hx hxN T hTM hTC hTpc ⟨eT⟩ hnt huniq
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hle, heq⟩ := comparison_ambient hM hx hxN hTM hTC hTpc
  have hlt : (pPrimeCore 2 T).index < (pPrimeCore 2 M).index :=
    lt_of_le_of_ne hle fun hidx => hnt (heq hidx).2
  obtain ⟨σ, hσ2, hfwd, hbwd, -⟩ := exists_fixedComponent_correspondence hM hx hxN
  obtain ⟨hPF, hPc⟩ := hfwd T hTM hTC hTpc
  obtain ⟨hPFC, hPex, ⟨eP⟩⟩ := layer_facts hM hx hxN hσ2 hTM hTC hTpc hPF hPc eT hlt
  have hMq : IsQuasisimple (↥M ⧸ pPrimeCore 2 ↥M) :=
    ((CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 M).mp hM).2.2
  have : IsSimpleGroup ((↥M ⧸ pPrimeCore 2 ↥M) ⧸ center (↥M ⧸ pPrimeCore 2 ↥M)) := hMq.2.1
  have hna := hMq.2.2
  have hcat : Blueprint.Catalog ((↥M ⧸ pPrimeCore 2 ↥M) ⧸ center (↥M ⧸ pPrimeCore 2 ↥M)) :=
    SectionRank.catalog_of_isKGroupCat_of_surjective hK M
      ((QuotientGroup.mk' (center (↥M ⧸ pPrimeCore 2 ↥M))).comp
        (QuotientGroup.mk' (pPrimeCore 2 ↥M)))
      ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
  have huniq' : ∀ P' : Subgroup ((↥M ⧸ pPrimeCore 2 ↥M) ⧸ center (↥M ⧸ pPrimeCore 2 ↥M)),
      ProperFixedComponent σ P' → P' = imageInSimple M T := by
    rintro P' ⟨-, hP'F, hP'c, -⟩
    obtain ⟨T'', hT''M, hT''C, hT''pc, hΦ⟩ := hbwd P' hP'F hP'c
    rw [← hΦ, huniq T'' hT''M hT''C hT''pc]
  rcases hleaf _ inferInstance hna hcat σ _ hPFC hPex ⟨eP⟩ huniq' with
    ⟨m, hm, hm7, ⟨eS⟩⟩ | hnon
  · exact Or.inl ⟨m, hm, hm7, exists_equiv_alt_of_fixed_component hMq hTM eT hPFC eP hm7 eS⟩
  · obtain ⟨eMS⟩ := GrSLit.nonempty_quotient_center_equiv_fusionZStar ↥M
    exact Or.inr (FivePumpNonAlt.of_mulEquiv eMS hnon)

end CFSG.ComponentClassification.SolMax.FiveCat
