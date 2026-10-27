module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenNineWTransfer
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexFiveLevi
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SUThreeTwoShape
import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.OddW
import CFSG.Adapters.GeneralizedFittingTop
import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.Cover

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus

open CFSG.AGLEmbedding Subgroup TenThreeThree CFSG.HardMathSupport.Solomon.LocalBalance

variable {X : Type*} [Group X]

theorem mem_of_pow_two_pow_eq_one {N : Subgroup X} [N.Normal] (hN : ¬ 2 ∣ N.index) {x : X}
    {k : ℕ} (hx : x ^ (2 ^ k) = 1) : x ∈ N := by
  have hi : N.index ≠ 0 := fun h => hN (h ▸ dvd_zero 2)
  haveI : N.FiniteIndex := ⟨hi⟩
  have hco : Nat.Coprime (2 ^ k) (Nat.card (X ⧸ N)) := by
    rw [← Subgroup.index]
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hN)
  have h1 : orderOf (QuotientGroup.mk x : X ⧸ N) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left
      (orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hx, QuotientGroup.mk_one])) hco)
      (orderOf_dvd_natCard _)
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h1
  exact h1

theorem closure_two_le_of_odd_index {N : Subgroup X} [N.Normal] (hN : ¬ 2 ∣ N.index) :
    closure {x : X | ∃ k : ℕ, x ^ (2 ^ k) = 1} ≤ N :=
  (closure_le N).mpr fun _ ⟨_, hx⟩ => mem_of_pow_two_pow_eq_one hN hx

theorem IsWBlock.eq_one_of_comm {X : Type} {A : Type*} [Group X] [Group A] [Finite A]
    (hX : IsWBlock X) (hA : Odd (Nat.card A)) (hcomm : ∀ a b : A, a * b = b * a) (f : X →* A)
    (x : X) : f x = 1 := by
  rcases hX with ⟨⟨hperf, -⟩, -⟩ | hs
  · have h : (⊤ : Subgroup X) ≤ f.ker := by
      rw [← hperf, commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm _ _
    exact h (mem_top x)
  · have hodd : ¬ 2 ∣ f.ker.index := by
      rw [Subgroup.index_ker]
      exact fun h => (Nat.not_even_iff_odd.mpr hA)
        (even_iff_two_dvd.mpr (h.trans (Subgroup.card_subgroup_dvd_card _)))
    have h := closure_two_le_of_odd_index hodd
    rw [IsSymThreeOrSUThreeTwo.closure_two kFactSUThreeTwoShape_holds hs] at h
    exact h (mem_top x)

theorem map_eq_one_of_pow_two_pow {X A : Type*} [Group X] [Group A] [Finite A]
    (hA : Odd (Nat.card A)) (f : X →* A) {x : X} {k : ℕ} (hx : x ^ (2 ^ k) = 1) : f x = 1 := by
  have hi : ¬ 2 ∣ (⊥ : Subgroup A).index := by
    rw [Subgroup.index_bot]
    exact fun h => (Nat.not_even_iff_odd.mpr hA) (even_iff_two_dvd.mpr h)
  exact (Subgroup.mem_bot).mp
    (mem_of_pow_two_pow_eq_one hi (by rw [← map_pow, hx, map_one]))

theorem wSup_le_map_of_odd_index {Q R : Type} [Group Q] [Group R] {τ : Q →* R}
    (hτ : Function.Surjective τ) {N : Subgroup Q} [hN : N.Normal] (hi : ¬ 2 ∣ N.index)
    (hc : commutator Q ≤ N) : wSup R ≤ N.map τ := by
  haveI : (N.map τ).Normal := hN.map τ hτ
  have hi' : ¬ 2 ∣ (N.map τ).index := fun h => hi (h.trans (Subgroup.index_map_dvd N hτ))
  refine iSup₂_le fun T hT => ?_
  have h1 : (⊤ : Subgroup ↥T).map T.subtype = T := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rcases hT with ⟨-, ⟨-, -, hperf, -⟩ | hs⟩
  · have hT : ⁅T, T⁆ = T := by
      calc ⁅T, T⁆ = ⁅(⊤ : Subgroup ↥T).map T.subtype, (⊤ : Subgroup ↥T).map T.subtype⁆ := by
            rw [h1]
        _ = (commutator ↥T).map T.subtype := (Subgroup.map_commutator _ _ _).symm
        _ = T := by rw [hperf, h1]
    calc T = ⁅T, T⁆ := hT.symm
      _ ≤ ⁅(⊤ : Subgroup R), ⊤⁆ := Subgroup.commutator_mono le_top le_top
      _ = (commutator Q).map τ := by
          rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective τ hτ]
      _ ≤ N.map τ := Subgroup.map_mono hc
  · have h := IsSymThreeOrSUThreeTwo.closure_two kFactSUThreeTwoShape_holds hs
    rw [← h1, ← h, MonoidHom.map_closure]
    refine (Subgroup.closure_mono ?_).trans (closure_two_le_of_odd_index hi')
    rintro _ ⟨x, ⟨k, hk⟩, rfl⟩
    exact ⟨k, by rw [Subgroup.coe_subtype, ← Subgroup.coe_pow, hk, Subgroup.coe_one]⟩

theorem exists_surjective_factor {A X R : Type*} [Group A] [Group X] [Group R] (ψ : A →* X)
    (hψ : Function.Surjective ψ) (g : A →* R) (h : ψ.ker ≤ g.ker) :
    ∃ f : X →* g.range, Function.Surjective f ∧ ∀ a, (f (ψ a) : R) = g a := by
  have h' : ψ.ker ≤ g.rangeRestrict.ker := by rw [MonoidHom.ker_rangeRestrict]; exact h
  refine ⟨ψ.liftOfSurjective hψ ⟨g.rangeRestrict, h'⟩, ?_, fun a => ?_⟩
  · rintro ⟨_, a, rfl⟩
    exact ⟨ψ a, by rw [MonoidHom.liftOfRightInverse_comp_apply]; rfl⟩
  · rw [MonoidHom.liftOfRightInverse_comp_apply]
    rfl

section Census

variable {Q R : Type} [Group Q] [Finite Q] [Group R] [Finite R]
variable {k : ℕ} {G : Fin k → Type} [∀ j, Group (G j)] [∀ j, Finite (G j)]

theorem le_ker_mk_comp_of_isPGroup_two (σ : Q →* R) (hσ : Function.Surjective σ)
    {M : Subgroup Q} [hM : M.Normal] (h2 : IsPGroup 2 M) :
    M ≤ ((QuotientGroup.mk' (CFSG.pCore 2 R)).comp σ).ker := by
  intro x hx
  have hle_pc : M.map σ ≤ CFSG.pCore 2 R := le_sSup ⟨hM.map σ hσ, h2.map σ⟩
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff]
  exact hle_pc (Subgroup.mem_map_of_mem σ hx)

abbrev blockPre (β : Q →* ∀ j, G j) (S : ∀ j, Subgroup (G j)) (j : Fin k) : Subgroup Q :=
  ((S j).map (MonoidHom.mulSingle G j)).comap β

theorem map_mulSingle_le_pi (S : ∀ j, Subgroup (G j)) (j : Fin k) :
    (S j).map (MonoidHom.mulSingle G j) ≤ Subgroup.pi Set.univ S := by
  rintro _ ⟨s, hs, rfl⟩
  exact (Subgroup.mulSingle_mem_pi j s).mpr fun _ => hs

theorem blockPre_le (β : Q →* ∀ j, G j) (S : ∀ j, Subgroup (G j)) (j : Fin k) :
    blockPre β S j ≤ (Subgroup.pi Set.univ S).comap β :=
  Subgroup.comap_mono (map_mulSingle_le_pi S j)

theorem mem_blockPre_iff {β : Q →* ∀ j, G j} {S : ∀ j, Subgroup (G j)} {j : Fin k} {x : Q} :
    x ∈ blockPre β S j ↔ β x j ∈ S j ∧ β x = Pi.mulSingle j (β x j) := by
  constructor
  · rintro ⟨s, hs, hsx⟩
    rw [← hsx, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same]
    exact ⟨hs, rfl⟩
  · rintro ⟨hs, hx⟩
    exact ⟨_, hs, hx.symm⟩

theorem comap_pi_le_iSup_sup_ker (β : Q →* ∀ j, G j) (S : ∀ j, Subgroup (G j))
    (hle : Subgroup.pi Set.univ S ≤ β.range) :
    (Subgroup.pi Set.univ S).comap β ≤ (⨆ j, blockPre β S j) ⊔ β.ker := by
  rw [← Subgroup.comap_map_eq]
  refine Subgroup.comap_mono (Subgroup.pi_le_iff.mpr fun j => ?_)
  have hmapB : (blockPre β S j).map β = (S j).map (MonoidHom.mulSingle G j) := by
    rw [Subgroup.map_comap_eq, inf_eq_right]
    exact (map_mulSingle_le_pi S j).trans hle
  rw [← hmapB]
  exact Subgroup.map_mono (le_iSup (blockPre β S) j)

theorem normal_comap_pi (β : Q →* ∀ j, G j) (S : ∀ j, Subgroup (G j))
    (hn : β.range ≤ normalizer (Subgroup.pi Set.univ S : Set (∀ j, G j))) :
    ((Subgroup.pi Set.univ S).comap β).Normal := ⟨fun n hnN x => by
  rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
  exact (Subgroup.mem_normalizer_iff.mp (hn ⟨x, rfl⟩) (β n)).mp hnN⟩

theorem normal_blockPre_subgroupOf (β : Q →* ∀ j, G j) (S : ∀ j, Subgroup (G j)) (j : Fin k) :
    ((blockPre β S j).subgroupOf ((Subgroup.pi Set.univ S).comap β)).Normal :=
  ⟨fun b hb n => by
    rw [Subgroup.mem_subgroupOf] at hb ⊢
    obtain ⟨s, hs, hsb⟩ := hb
    have hnj : β (n : Q) j ∈ S j := (Subgroup.mem_pi _).mp n.2 j (Set.mem_univ j)
    refine ⟨β (n : Q) j * s * (β (n : Q) j)⁻¹, (S j).mul_mem ((S j).mul_mem hnj hs)
      ((S j).inv_mem hnj), ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
    rw [← hsb]
    funext i
    by_cases hij : i = j
    · subst hij
      simp [Pi.mul_apply, Pi.inv_apply]
    · simp [Pi.mul_apply, Pi.inv_apply, hij]⟩

theorem exists_blockPre_factor (β : Q →* ∀ j, G j) (S : ∀ j, Subgroup (G j))
    (hle : Subgroup.pi Set.univ S ≤ β.range) (j : Fin k) {X : Type*} [Group X] (f : Q →* X)
    (hf : β.ker ≤ f.ker) :
    ∃ f' : ↥(S j) →* ↥((blockPre β S j).map f), Function.Surjective f' ∧
      ∀ x ∈ blockPre β S j, ∀ s : ↥(S j), (s : G j) = β x j → (f' s : X) = f x := by
  let ψ : ↥(blockPre β S j) →* ↥(S j) :=
    { toFun := fun x => ⟨β (x : Q) j, (mem_blockPre_iff.mp x.2).1⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun x y => by apply Subtype.ext; simp }
  have hψ : Function.Surjective ψ := by
    rintro ⟨s, hs⟩
    obtain ⟨x, hx⟩ := hle ((Subgroup.mulSingle_mem_pi j s).mpr fun _ => hs)
    refine ⟨⟨x, ⟨s, hs, hx.symm⟩⟩, Subtype.ext ?_⟩
    change β x j = s
    rw [hx, Pi.mulSingle_eq_same]
  have hker : ψ.ker ≤ (f.comp (blockPre β S j).subtype).ker := fun x hx => by
    apply hf
    change β (x : Q) = 1
    rw [(mem_blockPre_iff.mp x.2).2]
    have : β (x : Q) j = 1 := congrArg Subtype.val hx
    rw [this, Pi.mulSingle_one]
  obtain ⟨f', hf', hfψ⟩ := exists_surjective_factor ψ hψ _ hker
  have hr : (f.comp (blockPre β S j).subtype).range = (blockPre β S j).map f := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  refine ⟨(MulEquiv.subgroupCongr hr).toMonoidHom.comp f',
    (MulEquiv.subgroupCongr hr).surjective.comp hf', fun x hx s hs => ?_⟩
  have hs' : s = ψ ⟨x, hx⟩ := Subtype.ext hs
  rw [hs']
  exact hfψ ⟨x, hx⟩

theorem map_comap_pi_le_wSup (σ : Q →* R) (hσ : Function.Surjective σ)
    (hc : σ.ker ≤ center Q) (ho : Odd (Nat.card σ.ker)) (β : Q →* ∀ j, G j)
    (S : ∀ j, Subgroup (G j)) (h2 : IsPGroup 2 β.ker) (hle : Subgroup.pi Set.univ S ≤ β.range)
    (hn : β.range ≤ normalizer (Subgroup.pi Set.univ S : Set (∀ j, G j)))
    (hodd : Odd ((Subgroup.pi Set.univ S).relIndex β.range))
    (hW : ∀ j, S j = ⊥ ∨ IsWBlock ↥(S j))
    (hZ : ∀ j, ¬ CFSG.Open.IsQuasisimple ↥(S j) → ∀ z ∈ σ.ker,
      β z ∈ (S j).map (MonoidHom.mulSingle G j) → β z = 1) :
    ((Subgroup.pi Set.univ S).comap β).map ((QuotientGroup.mk' (CFSG.pCore 2 R)).comp σ) ≤
      wSup (R ⧸ CFSG.pCore 2 R) := by
  classical
  set τ : Q →* R ⧸ CFSG.pCore 2 R := (QuotientGroup.mk' (CFSG.pCore 2 R)).comp σ with hτdef
  have hτ : Function.Surjective τ := (QuotientGroup.mk'_surjective _).comp hσ
  have hpcΛ : CFSG.pCore 2 ↥β.range = ⊥ :=
    pCore_two_eq_bot_of_le_normalizer_of_odd_relIndex hle hn hodd hW
  have hpc_le : CFSG.pCore 2 Q ≤ β.ker := by
    have hnorm : ((CFSG.pCore 2 Q).map β.rangeRestrict).Normal :=
      (CFSG.pCore_normal (p := 2) (G := Q)).map β.rangeRestrict
        (MonoidHom.rangeRestrict_surjective β)
    have h2' : IsPGroup 2 ((CFSG.pCore 2 Q).map β.rangeRestrict) :=
      (CFSG.pCore_isPGroup (p := 2) (G := Q)).map β.rangeRestrict
    have hle_pc : (CFSG.pCore 2 Q).map β.rangeRestrict ≤ CFSG.pCore 2 ↥β.range :=
      le_sSup ⟨hnorm, h2'⟩
    rw [hpcΛ, le_bot_iff, Subgroup.map_eq_bot_iff, MonoidHom.ker_rangeRestrict] at hle_pc
    exact hle_pc
  have hβτ : β.ker ≤ τ.ker := le_ker_mk_comp_of_isPGroup_two σ hσ h2
  have hτker : τ.ker ≤ σ.ker ⊔ β.ker := by
    let H : Subgroup Q := (CFSG.pCore 2 R).comap σ
    have hτH : τ.ker = H := by
      ext x
      rw [MonoidHom.mem_ker, hτdef, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      rfl
    have hHN : H.Normal := (CFSG.pCore_normal (p := 2) (G := R)).comap σ
    have hZH : σ.ker ≤ H := by
      intro z hz
      rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hz]
      exact (CFSG.pCore 2 R).one_mem
    haveI hZn : (σ.ker.subgroupOf H).Normal := (inferInstance : σ.ker.Normal).subgroupOf H
    have hquot : IsPGroup 2 (↥H ⧸ σ.ker.subgroupOf H) := by
      let g : ↥H →* R := σ.domRestrict H
      have hker : g.ker = σ.ker.subgroupOf H := MonoidHom.ker_domRestrict H σ
      have hrange : g.range = CFSG.pCore 2 R := by
        ext r
        constructor
        · rintro ⟨x, -, rfl⟩
          exact x.2
        · intro hr
          obtain ⟨q, hq⟩ := hσ r
          exact ⟨⟨q, by rw [Subgroup.mem_comap, hq]; exact hr⟩, hq⟩
      have e : (↥H ⧸ σ.ker.subgroupOf H) ≃* ↥(CFSG.pCore 2 R) :=
        ((QuotientGroup.quotientMulEquivOfEq hker).symm.trans
          (QuotientGroup.quotientKerEquivRange g)).trans (MulEquiv.subgroupCongr hrange)
      exact (CFSG.pCore_isPGroup (p := 2) (G := R)).of_equiv e.symm
    rw [hτH]
    calc H ≤ σ.ker ⊔ CFSG.pCore 2 Q :=
          le_sup_pCore_two_of_central_odd_quotient_two hHN hZH hc ho hquot
      _ ≤ σ.ker ⊔ β.ker := sup_le le_sup_left (hpc_le.trans le_sup_right)
  set N : Subgroup Q := (Subgroup.pi Set.univ S).comap β with hNdef
  have hNn : N.Normal := normal_comap_pi β S hn
  have hblock : ∀ j, (blockPre β S j).map τ ≤ wSup (R ⧸ CFSG.pCore 2 R) := by
    intro j
    have hsub : CFSG.Open.IsSubnormal ((blockPre β S j).map τ) ⊤ := by
      refine (CFSG.Adapters.isSubnormal_top_iff _).mpr (Subgroup.IsSubnormal.map hτ ?_)
      exact Subgroup.IsSubnormal.step _ N (blockPre_le β S j) hNn.isSubnormal
        (normal_blockPre_subgroupOf β S j)
    obtain ⟨f, hf, hfψ⟩ := exists_blockPre_factor β S hle j τ hβτ
    rcases hW j with hbot | hWj
    · haveI : Subsingleton ↥(S j) := by rw [hbot]; infer_instance
      intro y hy
      obtain ⟨s, hs⟩ := hf ⟨y, hy⟩
      rw [Subsingleton.elim s 1, map_one] at hs
      have : y = 1 := (congrArg Subtype.val hs).symm
      rw [this]
      exact one_mem _
    by_cases hq : CFSG.Open.IsQuasisimple ↥(S j)
    · by_cases hbotg : (blockPre β S j).map τ = ⊥
      · rw [hbotg]
        exact bot_le
      haveI : Nontrivial ↥((blockPre β S j).map τ) := (Subgroup.nontrivial_iff_ne_bot _).mpr hbotg
      exact le_wSup_of_subnormal_of_isQuasisimple hsub
        (Lemma512Ns.isQuasisimple_of_surjective_of_nontrivial hq f hf)
    · have hsym : IsSymThreeOrSUThreeTwo ↥(S j) := by
        rcases hWj with ⟨hq', -⟩ | hs
        · exact absurd hq' hq
        · exact hs
      have hfi : Function.Injective f := by
        refine (injective_iff_map_eq_one f).mpr fun s hs => ?_
        obtain ⟨x, hx, hxs⟩ : ∃ x ∈ blockPre β S j, (s : G j) = β x j := by
          obtain ⟨x, hx⟩ := hle ((Subgroup.mulSingle_mem_pi j (s : G j)).mpr fun _ => s.2)
          exact ⟨x, ⟨s, s.2, hx.symm⟩, by rw [hx, Pi.mulSingle_eq_same]⟩
        have hgx : τ x = 1 := by
          rw [← hfψ x hx s hxs, hs]
          rfl
        have hx' := hτker hgx
        rw [Subgroup.mem_sup_of_normal_left] at hx'
        obtain ⟨z, hz, b, hb, hzb⟩ := hx'
        have hβx : β x = β z := by
          rw [← hzb, map_mul, MonoidHom.mem_ker.mp hb, mul_one]
        have hz1 : β z = 1 := hZ j hq z hz (hβx ▸ hx)
        apply Subtype.ext
        rw [hxs, hβx, hz1, Pi.one_apply]
        rfl
      exact le_wSup_of_subnormal_of_symThree hsub
        (IsSymThreeOrSUThreeTwo.of_mulEquiv (MulEquiv.ofBijective f ⟨hfi, hf⟩) hsym)
  calc N.map τ ≤ ((⨆ j, blockPre β S j) ⊔ β.ker).map τ :=
        Subgroup.map_mono (comap_pi_le_iSup_sup_ker β S hle)
    _ = (⨆ j, (blockPre β S j).map τ) ⊔ (β.ker).map τ := by
        rw [Subgroup.map_sup, Subgroup.map_iSup]
    _ ≤ wSup (R ⧸ CFSG.pCore 2 R) := by
        rw [(Subgroup.map_eq_bot_iff _).mpr hβτ, sup_bot_eq]
        exact iSup_le hblock

theorem eqOn_comap_pi_of_central {L' : Type*} [Group L'] [Finite L']
    (hZL : Odd (Nat.card (center L'))) (θ₁ θ₂ : Q →* L')
    (h : ∀ x, θ₁ x * (θ₂ x)⁻¹ ∈ center L') (β : Q →* ∀ j, G j) (S : ∀ j, Subgroup (G j))
    (hle : Subgroup.pi Set.univ S ≤ β.range) (hW : ∀ j, S j = ⊥ ∨ IsWBlock ↥(S j))
    (h2 : IsPGroup 2 β.ker) : ∀ x ∈ (Subgroup.pi Set.univ S).comap β, θ₁ x = θ₂ x := by
  let D : Q →* ↥(center L') :=
    { toFun := fun x => ⟨θ₁ x * (θ₂ x)⁻¹, h x⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun x y => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, map_mul, mul_inv_rev]
        have hy := Subgroup.mem_center_iff.mp (h y) (θ₁ x)
        have hx := Subgroup.mem_center_iff.mp (h x) (θ₁ y * (θ₂ y)⁻¹)
        calc θ₁ x * θ₁ y * ((θ₂ y)⁻¹ * (θ₂ x)⁻¹) =
            (θ₁ x * (θ₁ y * (θ₂ y)⁻¹)) * (θ₂ x)⁻¹ := by group
          _ = (θ₁ y * (θ₂ y)⁻¹) * θ₁ x * (θ₂ x)⁻¹ := by rw [hy]
          _ = (θ₁ y * (θ₂ y)⁻¹) * (θ₁ x * (θ₂ x)⁻¹) := by group
          _ = (θ₁ x * (θ₂ x)⁻¹) * (θ₁ y * (θ₂ y)⁻¹) := hx }
  have hcomm : ∀ a b : ↥(center L'), a * b = b * a := fun a b =>
    Subtype.ext (Subgroup.mem_center_iff.mp b.2 a)
  have hkerβ : β.ker ≤ D.ker := fun x hx => by
    obtain ⟨n, hn⟩ := h2 ⟨x, hx⟩
    have hx' : x ^ (2 ^ n) = 1 := by simpa using congrArg Subtype.val hn
    exact map_eq_one_of_pow_two_pow hZL D hx'
  have hB : ∀ j, blockPre β S j ≤ D.ker := by
    intro j x hx
    obtain ⟨f, -, hfψ⟩ := exists_blockPre_factor β S hle j D hkerβ
    have h1 := hfψ x hx ⟨β x j, (mem_blockPre_iff.mp hx).1⟩ rfl
    rw [MonoidHom.mem_ker, ← h1]
    rcases hW j with hbot | hWj
    · haveI : Subsingleton ↥(S j) := by rw [hbot]; infer_instance
      rw [Subsingleton.elim (⟨β x j, (mem_blockPre_iff.mp hx).1⟩ : ↥(S j)) 1, map_one]
      rfl
    · exact IsWBlock.eq_one_of_comm hWj hZL hcomm (((blockPre β S j).map D).subtype.comp f) _
  intro x hx
  have hxD : x ∈ D.ker := ((comap_pi_le_iSup_sup_ker β S hle).trans
    (sup_le (iSup_le hB) hkerβ)) hx
  exact mul_inv_eq_one.mp (congrArg Subtype.val (MonoidHom.mem_ker.mp hxD))

theorem pow_conj_eq_of_central (β : Q →* ∀ j, G j) (S : ∀ j, Subgroup (G j))
    (hle : Subgroup.pi Set.univ S ≤ β.range) (φ : MulAut Q) (g : ∀ j, G j)
    (hφ : ∀ x, β (φ x) = g * β x * g⁻¹) (hgN : ∀ j, ∀ s ∈ S j, g j * s * (g j)⁻¹ ∈ S j)
    (n : ℕ) (Z : Subgroup Q) (hZc : Z ≤ center Q)
    (hZW : ∀ j, ¬ CFSG.Open.IsQuasisimple ↥(S j) → ∀ z ∈ Z,
      β z ∈ (S j).map (MonoidHom.mulSingle G j) → β z = 1)
    (hφZ : ∀ x ∈ (Subgroup.pi Set.univ S).comap β, (φ ^ n) x * x⁻¹ ∈ Z) :
    ∀ j, ∀ s ∈ S j, g j ^ n * s * (g j ^ n)⁻¹ = s := by
  intro j
  have hgNn : ∀ i : ℕ, ∀ s ∈ S j, g j ^ i * s * (g j ^ i)⁻¹ ∈ S j := by
    intro i
    induction i with
    | zero => intro s hs; simpa using hs
    | succ i ih =>
      intro s hs
      have e : g j ^ (i + 1) * s * (g j ^ (i + 1))⁻¹ = g j * (g j ^ i * s * (g j ^ i)⁻¹) *
          (g j)⁻¹ := by rw [pow_succ']; group
      rw [e]
      exact hgN j _ (ih s hs)
  have hkey : ∀ s ∈ S j, ∃ c ∈ Z, β c = Pi.mulSingle j (g j ^ n * s * (g j ^ n)⁻¹ * s⁻¹) := by
    intro s hs
    have hsp : Pi.mulSingle j s ∈ Subgroup.pi Set.univ S :=
      (Subgroup.mulSingle_mem_pi j s).mpr fun _ => hs
    obtain ⟨x, hx⟩ := hle hsp
    have hxN : x ∈ (Subgroup.pi Set.univ S).comap β := by
      rw [Subgroup.mem_comap, hx]
      exact hsp
    refine ⟨(φ ^ n) x * x⁻¹, hφZ x hxN, ?_⟩
    rw [map_mul, map_inv, KFactProofs.FieldIndex.beta_pow_apply β φ g hφ n x, hx]
    funext i
    by_cases hij : i = j
    · subst hij
      simp [Pi.mul_apply, Pi.inv_apply, Pi.pow_apply]
    · simp [Pi.mul_apply, Pi.inv_apply, Pi.pow_apply, hij]
  by_cases hq : CFSG.Open.IsQuasisimple ↥(S j)
  · let f₁ : ↥(S j) →* ↥(S j) :=
      ((MulAut.conj (g j ^ n)).toMonoidHom.comp (S j).subtype).codRestrict (S j)
        fun s => hgNn n s s.2
    have hcen : ∀ s ∈ (⊤ : Subgroup ↥(S j)),
        f₁ s * (MonoidHom.id ↥(S j) s)⁻¹ ∈ center ↥(S j) := by
      intro s _
      obtain ⟨c, hc, hcβ⟩ := hkey s s.2
      rw [Subgroup.mem_center_iff]
      intro t
      apply Subtype.ext
      obtain ⟨y, hy⟩ := hle ((Subgroup.mulSingle_mem_pi j (t : G j)).mpr fun _ => t.2)
      have h1 : β (y * c) = β (c * y) := by
        rw [(Subgroup.mem_center_iff.mp (hZc hc) y)]
      rw [map_mul, map_mul, hy, hcβ] at h1
      have h2 := congrFun h1 j
      simp only [Pi.mul_apply, Pi.mulSingle_eq_same] at h2
      exact h2
    have hperf : ⁅(⊤ : Subgroup ↥(S j)), ⊤⁆ = ⊤ := hq.1
    intro s hs
    have h3 := KFactProofs.FieldIndex.eqOn_of_perfect_central f₁ (MonoidHom.id _) hperf hcen
      ⟨s, hs⟩ (mem_top _)
    exact congrArg Subtype.val h3
  · intro s hs
    obtain ⟨c, hc, hcβ⟩ := hkey s hs
    have hmem : β c ∈ (S j).map (MonoidHom.mulSingle G j) :=
      ⟨_, mul_mem (hgNn n s hs) (inv_mem hs), hcβ.symm⟩
    have h1 := hZW j hq c hc hmem
    rw [hcβ] at h1
    have h2 := congrFun h1 j
    rw [Pi.mulSingle_eq_same, Pi.one_apply, mul_inv_eq_one] at h2
    exact h2

end Census

section Transport

open KFactProofs.FieldIndex KFactProofs.FieldIndexP CFSG.Open
open scoped commutatorElement

theorem actsInnerlyW_of_levi_dataP {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {Y : Type} [Group Y] [Finite Y] {L P : Subgroup Y} [L.Normal] (hPL : P ≤ L)
    (hZL : Odd (Nat.card (center ↥L)))
    {K : Type} [Group K] [Finite K] (ρ : K →* ↥L) (hρ : Function.Surjective ρ)
    (hker : ρ.ker ≤ center K) (hρo : Odd (Nat.card ρ.ker)) (Q : Subgroup K)
    (hQ : Q = coverSub ρ P) {k : ℕ} {G : Fin k → Type} [∀ j, Group (G j)] [∀ j, Finite (G j)]
    (S H : ∀ j, Subgroup (G j)) (β : ↥Q →* ∀ j, G j)
    (h2 : IsPGroup 2 β.ker) (hS : Subgroup.pi Set.univ S ≤ β.range)
    (hc : ⁅β.range, β.range⁆ ≤ Subgroup.pi Set.univ S)
    (hodd : Odd ((Subgroup.pi Set.univ S).relIndex β.range))
    (hW : ∀ j, S j = ⊥ ∨ IsWBlock ↥(S j))
    (hblock : ∀ j, S j ≠ ⊥ → BlockOKP p (H j) (S j))
    (hZ : ∀ (j : Fin k) (E : Subgroup (G j)), E ≤ S j → IsElemAbelian p E → Nat.card E = p ^ 2 →
      ∀ x : ↥Q, ρ (x : K) = 1 → β x ∈ E.map (MonoidHom.mulSingle G j) → x = 1)
    (hZW : ∀ j, ¬ CFSG.Open.IsQuasisimple ↥(S j) → ∀ x : ↥Q, ρ (x : K) = 1 →
      β x ∈ (S j).map (MonoidHom.mulSingle G j) → β x = 1)
    (φ : MulAut ↥Q) (g : ∀ j, G j) (hg : ∀ j, g j ∈ H j)
    (hφ : ∀ x, β (φ x) = g * β x * g⁻¹) (hgN : ∀ j, ∀ s ∈ S j, g j * s * (g j)⁻¹ ∈ S j)
    {a : Y} (ha : a ∈ normalizer (P : Set Y))
    (hcompat : ∀ x : ↥Q,
      (MulAut.conjNormal a : MulAut ↥L) (ρ (x : K)) * (ρ ((φ x : ↥Q) : K))⁻¹ ∈ center ↥L)
    (hpow : ∃ m : ℕ, ∀ w ∈ wPre P, a ^ (p ^ m) * w = w * a ^ (p ^ m))
    (hrk : Open.pRank p (wPre P) ≤ 1) :
    ∃ v ∈ wPre P, ∀ w ∈ wPre P, ⁅a * v, w⁆ ∈ pCoreOf 2 P := by
  subst hQ
  classical
  obtain ⟨m, hm⟩ := hpow
  set τ₀ := coverHomY ρ P with hτ₀
  let σ : ↥(coverSub ρ P) →* ↥P := τ₀.codRestrict P fun x => x.2
  have hσ : Function.Surjective σ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx⟩ := hρ ⟨y, hPL hy⟩
    refine ⟨⟨x, ?_⟩, Subtype.ext ?_⟩
    · change ρ x ∈ P.subgroupOf L
      rw [hx]
      exact hy
    · change ((ρ x : ↥L) : Y) = y
      rw [hx]
  have hσker : ∀ x, σ x = 1 ↔ ρ (x : K) = 1 := fun x => by
    constructor
    · intro h
      have h' := congrArg Subtype.val h
      exact Subtype.ext h'
    · intro h
      apply Subtype.ext
      change ((ρ (x : K) : ↥L) : Y) = 1
      rw [h]
      rfl
  have hσc : σ.ker ≤ center _ := fun x hx =>
    coverHom_ker_le_center ρ hker P ((hσker x).mp hx)
  have hσo : Odd (Nat.card σ.ker) := by
    have hle : σ.ker.map (coverSub ρ P).subtype ≤ ρ.ker := by
      rintro _ ⟨x, hx, rfl⟩
      exact (hσker x).mp hx
    have h1 := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective (coverSub ρ P).subtype_injective] at h1
    exact hρo.of_dvd_nat h1
  have hZW' : ∀ j, ¬ CFSG.Open.IsQuasisimple ↥(S j) → ∀ z ∈ σ.ker,
      β z ∈ (S j).map (MonoidHom.mulSingle G j) → β z = 1 := fun j hj z hz =>
    hZW j hj z ((hσker z).mp hz)
  set N : Subgroup ↥(coverSub ρ P) := (Subgroup.pi Set.univ S).comap β with hNdef
  set τ := (QuotientGroup.mk' (CFSG.pCore 2 ↥P)).comp σ with hτdef
  have hτ : Function.Surjective τ := (QuotientGroup.mk'_surjective _).comp hσ
  have hn := le_normalizer_of_commutator_le hS hc
  haveI hNn : N.Normal := normal_comap_pi β S hn
  have hWB : N.map τ ≤ wSup (↥P ⧸ CFSG.pCore 2 ↥P) :=
    map_comap_pi_le_wSup σ hσ hσc hσo β S h2 hS hn hodd hW hZW'
  have hWA : wSup (↥P ⧸ CFSG.pCore 2 ↥P) ≤ N.map τ := by
    refine wSup_le_map_of_odd_index hτ ?_ ?_
    · rw [hNdef, Subgroup.index_comap]
      exact fun h => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)
    · rw [hNdef, ← Subgroup.map_le_iff_le_comap, _root_.commutator_def, Subgroup.map_commutator,
        ← MonoidHom.range_eq_map]
      exact hc
  have hW1 : ∀ x ∈ N, τ₀ x ∈ wPre P := fun x hx => ⟨σ x, hWB ⟨x, hx, rfl⟩, rfl⟩
  have hW2 : ∀ w ∈ wPre P, ∃ y ∈ N, ∃ o ∈ pCoreOf 2 P, w = τ₀ y * o := by
    rintro _ ⟨w', hw', rfl⟩
    obtain ⟨y, hy, hyw⟩ := hWA hw'
    have hyw' : (σ y)⁻¹ * w' ∈ CFSG.pCore 2 ↥P := QuotientGroup.eq.mp hyw
    refine ⟨y, hy, (((σ y)⁻¹ * w' : ↥P) : Y), ⟨_, hyw', rfl⟩, ?_⟩
    change (w' : Y) = ((σ y : ↥P) : Y) * (((σ y)⁻¹ * w' : ↥P) : Y)
    rw [← Subgroup.coe_mul, mul_inv_cancel_left]
  have hβO : ∀ x ∈ β.ker, τ₀ x ∈ pCoreOf 2 P := fun x hx => by
    have h1 : τ x = 1 := le_ker_mk_comp_of_isPGroup_two σ hσ h2 hx
    rw [hτdef, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact ⟨σ x, h1, rfl⟩
  have hex : ∀ x ∈ N, a * τ₀ x * a⁻¹ = τ₀ (φ x) := by
    intro x hx
    have h1 := eqOn_comap_pi_of_central hZL
      ((MulAut.conjNormal a : MulAut ↥L).toMonoidHom.comp (coverHom ρ P))
      ((coverHom ρ P).comp φ.toMonoidHom) hcompat β S hS hW h2 x hx
    have h2' := congrArg Subtype.val h1
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conjNormal_apply] at h2'
    exact h2'
  have hφN : ∀ x ∈ N, φ x ∈ N := by
    intro x hx
    rw [hNdef, Subgroup.mem_comap, hφ, Subgroup.mem_pi]
    intro j _
    exact hgN j _ ((Subgroup.mem_pi _).mp hx j (Set.mem_univ j))
  have hφNn : ∀ n : ℕ, ∀ x ∈ N, (φ ^ n) x ∈ N := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih =>
      intro x hx
      rw [pow_succ', MulAut.mul_apply]
      exact hφN _ (ih x hx)
  have hexn : ∀ n : ℕ, ∀ x ∈ N, a ^ n * τ₀ x * (a ^ n)⁻¹ = τ₀ ((φ ^ n) x) := by
    intro n
    induction n with
    | zero => intro x _; simp
    | succ n ih =>
      intro x hx
      rw [pow_succ' a, pow_succ' φ, MulAut.mul_apply, ← hex _ (hφNn n x hx), ← ih x hx]
      group
  have hcent : ∀ j, ∀ s ∈ S j, g j ^ (p ^ m) * s * (g j ^ (p ^ m))⁻¹ = s := by
    refine pow_conj_eq_of_central β S hS φ g hφ hgN (p ^ m) σ.ker hσc hZW' fun x hx => ?_
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    change τ₀ ((φ ^ (p ^ m)) x * x⁻¹) = 1
    rw [map_mul, map_inv, ← hexn _ x hx, hm _ (hW1 x hx)]
    group
  have hE : ∀ j, ∀ E : Subgroup (G j), E ≤ S j → IsElemAbelian p E → Nat.card E = p ^ 2 →
      False := by
    intro j E hES hE hcard
    have hÊel : IsElemAbelian p (E.map (MonoidHom.mulSingle G j)) :=
      CFSG.SectionRank.isElemAbelian_map hE _
    have hÊcard : Nat.card (E.map (MonoidHom.mulSingle G j)) = p ^ 2 := by
      rw [Subgroup.card_map_of_injective (f := MonoidHom.mulSingle G j)
        (Pi.mulSingle_injective j), hcard]
    have hEV : E.map (MonoidHom.mulSingle G j) ≤ N.map β := by
      rw [hNdef, Subgroup.map_comap_eq, inf_eq_right.mpr hS]
      exact (Subgroup.map_mono hES).trans (map_mulSingle_le_pi S j)
    obtain ⟨E', hE'V, hE'el, hE'card, hE'β, -⟩ := exists_lift_elemAbelianP hp2 β h2 hEV hÊel
    have hθinj : ∀ x ∈ E', τ₀ x = 1 → x = 1 := fun x hx h1 =>
      hZ j E hES hE hcard x (Subtype.ext h1) (hE'β x hx)
    have hE''V : E'.map τ₀ ≤ wPre P := by
      rintro _ ⟨x, hx, rfl⟩
      exact hW1 x (hE'V hx)
    have hE''el : IsElemAbelian p (E'.map τ₀) := CFSG.SectionRank.isElemAbelian_map hE'el _
    have hE''card : Nat.card (E'.map τ₀) = p ^ 2 := by
      have hbij : Function.Bijective (fun x : E' => (⟨τ₀ x, ⟨x, x.2, rfl⟩⟩ : E'.map τ₀)) := by
        refine ⟨fun x y hxy => ?_, fun y => ?_⟩
        · have h1 : τ₀ ((x : ↥(coverSub ρ P))⁻¹ * y) = 1 := by
            rw [map_mul, map_inv]
            have := congrArg Subtype.val hxy
            simp only at this
            rw [this, inv_mul_cancel]
          have := hθinj _ (E'.mul_mem (E'.inv_mem x.2) y.2) h1
          exact Subtype.ext (inv_mul_eq_one.1 this)
        · obtain ⟨z, hz, hzy⟩ := y.2
          exact ⟨⟨z, hz⟩, Subtype.ext hzy⟩
      rw [← Nat.card_congr (Equiv.ofBijective _ hbij), hE'card, hÊcard]
    have := CFSG.SectionRank.le_pRank (Fact.out : p.Prime).one_lt hE''V hE''el hE''card
    omega
  have hall : ∀ j, ∃ u ∈ S j, ∀ t ∈ S j, g j * t * (g j)⁻¹ = u * t * u⁻¹ := by
    intro j
    by_cases hbot : S j = ⊥
    · refine ⟨1, one_mem _, fun t ht => ?_⟩
      rw [hbot, Subgroup.mem_bot] at ht
      rw [ht]
      group
    · rcases hblock j hbot (g j) (hg j) (hgN j) m (hcent j) with h | ⟨E, hES, hEel, hEc⟩
      · exact h
      · exact (hE j E hES hEel hEc).elim
  choose u hu hconj using hall
  obtain ⟨y₀, hy₀⟩ := hS ((Subgroup.mem_pi _).mpr fun j _ => hu j)
  have hy₀N : y₀ ∈ N := by
    rw [hNdef, Subgroup.mem_comap, hy₀, Subgroup.mem_pi]
    exact fun j _ => hu j
  refine ⟨τ₀ y₀⁻¹, hW1 _ (inv_mem hy₀N), fun w hw => ?_⟩
  obtain ⟨y, hy, o, ho, rfl⟩ := hW2 w hw
  set y' := y₀⁻¹ * y * y₀ with hy'
  have hy'N : y' ∈ N := mul_mem (mul_mem (inv_mem hy₀N) hy) hy₀N
  have hβ : β (φ y') = β y := by
    rw [hφ, hy', map_mul, map_mul, map_inv, hy₀]
    funext j
    have hyj : β y j ∈ S j := (Subgroup.mem_pi _).mp hy j (Set.mem_univ j)
    have ht : (u j)⁻¹ * β y j * u j ∈ S j :=
      mul_mem (mul_mem (inv_mem (hu j)) hyj) (hu j)
    have h1 := hconj j _ ht
    simp only [Pi.mul_apply, Pi.inv_apply]
    rw [h1]
    group
  have hk : φ y' * y⁻¹ ∈ β.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hβ, mul_inv_cancel]
  have hA : (a * τ₀ y₀⁻¹) * τ₀ y * (a * τ₀ y₀⁻¹)⁻¹ = τ₀ (φ y' * y⁻¹) * τ₀ y := by
    rw [map_mul τ₀ (φ y'), map_inv τ₀ y, inv_mul_cancel_right, ← hex y' hy'N, hy', map_mul,
      map_mul, map_inv]
    group
  have hAN : a * τ₀ y₀⁻¹ ∈ normalizer (P : Set Y) :=
    mul_mem ha (le_normalizer (wPre_le P (hW1 _ (inv_mem hy₀N))))
  have hAO := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 P hAN
  have hyO := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 P
    (le_normalizer (σ y).2)
  have e : ⁅a * τ₀ y₀⁻¹, τ₀ y * o⁆ = ((a * τ₀ y₀⁻¹) * τ₀ y * (a * τ₀ y₀⁻¹)⁻¹) * (τ₀ y)⁻¹ *
      (τ₀ y * ((a * τ₀ y₀⁻¹) * o * (a * τ₀ y₀⁻¹)⁻¹ * o⁻¹) * (τ₀ y)⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [e, hA, mul_inv_cancel_right]
  refine mul_mem (hβO _ hk) ((mem_normalizer_iff.mp hyO _).mp (mul_mem ?_ (inv_mem ho)))
  exact (mem_normalizer_iff.mp hAO o).mp ho

end Transport

end CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus
