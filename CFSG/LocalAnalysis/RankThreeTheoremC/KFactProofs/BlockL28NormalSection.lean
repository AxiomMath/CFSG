module

import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockL28ProdSimple
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockNormal
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGroups
import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviCover
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockThreeFivesGroup
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFactsGlue

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open CFSG.AGLEmbedding
open scoped commutatorElement

section NormalSection

variable {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type} [∀ j, Group (G j)]

theorem exists_attached_block_of_normal_section [∀ j, Finite (G j)] {S : ∀ j, Subgroup (G j)}
    {X : Subgroup (∀ j, G j)} (hSX : Subgroup.pi Set.univ S ≤ X)
    (hXX : ⁅X, X⁆ ≤ Subgroup.pi Set.univ S)
    (hS : ∀ j, CFSG.Open.IsQuasisimple (S j) ∨ Group.IsSolvable (S j))
    {N : Subgroup (∀ j, G j)} (hNX : N ≤ X)
    (hN : X ≤ Subgroup.normalizer (N : Set (∀ j, G j)))
    {T : Type} [Group T] [IsSimpleGroup T] (hT : ∃ a b : T, a * b ≠ b * a)
    (f : ↥N →* T) (hf : Function.Surjective f) :
    ∃ j, CFSG.Open.IsQuasisimple (S j) ∧ (∀ s ∈ S j, (Pi.mulSingle j s : ∀ i, G i) ∈ N) ∧
      Nat.card T = Nat.card (↥(S j) ⧸ Subgroup.center ↥(S j)) ∧
      ∀ t : T, ∃ s ∈ S j, ∃ hs : (Pi.mulSingle j s : ∀ i, G i) ∈ N,
        f ⟨Pi.mulSingle j s, hs⟩ = t := by
  classical
  have hTc : ¬ ∀ a b : T, a * b = b * a := fun h => by
    obtain ⟨a, b, hab⟩ := hT
    exact hab (h a b)
  have hconj : ∀ x ∈ X, ∀ m ∈ Subgroup.pi Set.univ S, x * m * x⁻¹ ∈ Subgroup.pi Set.univ S := by
    intro x hx m hm
    have e : x * m * x⁻¹ = ⁅x, m⁆ * m := by rw [commutatorElement_def]; group
    rw [e]
    exact Subgroup.mul_mem _ (hXX (Subgroup.commutator_mem_commutator hx (hSX hm))) hm
  set F : Finset ι → Subgroup T :=
    fun A => ((LeviBlock.normalSupp N S A).subgroupOf N).map f with hFdef
  have hFn : ∀ A, (F A).Normal := by
    intro A
    refine Subgroup.Normal.map ⟨fun n hn g => ?_⟩ f hf
    rw [Subgroup.mem_subgroupOf, LeviBlock.mem_normalSupp] at hn ⊢
    obtain ⟨hnN, hnS, hnA⟩ := hn
    refine ⟨N.mul_mem (N.mul_mem g.2 hnN) (N.inv_mem g.2), fun j => ?_, fun j hj => ?_⟩
    · have := hconj _ (hNX g.2) _ ((Subgroup.mem_pi _).mpr fun i _ => hnS i)
      exact (Subgroup.mem_pi _).mp this j (Set.mem_univ j)
    · simp [Pi.mul_apply, Pi.inv_apply, hnA j hj]
  have hFbot_or_top : ∀ A, F A = ⊥ ∨ F A = ⊤ := fun A => by
    have := hFn A
    exact IsSimpleGroup.eq_bot_or_eq_top_of_normal (F A)
  have hFuniv : F Finset.univ = ⊤ := by
    rcases hFbot_or_top Finset.univ with h | h
    · exfalso
      refine hTc fun a b => ?_
      obtain ⟨n, rfl⟩ := hf a
      obtain ⟨m, rfl⟩ := hf b
      have hc : ⁅n, m⁆ ∈ (LeviBlock.normalSupp N S Finset.univ).subgroupOf N := by
        rw [Subgroup.mem_subgroupOf, LeviBlock.mem_normalSupp]
        have hcm : ((⁅n, m⁆ : ↥N) : ∀ j, G j) = ⁅(n : ∀ j, G j), (m : ∀ j, G j)⁆ := rfl
        refine ⟨(⁅n, m⁆ : ↥N).2, fun j => ?_, fun j hj => absurd (Finset.mem_univ j) hj⟩
        rw [hcm]
        exact (Subgroup.mem_pi _).mp (hXX (Subgroup.commutator_mem_commutator (hNX n.2) (hNX m.2)))
          j (Set.mem_univ j)
      have h1 : f ⁅n, m⁆ = 1 := by
        have := Subgroup.mem_map_of_mem f hc
        change f ⁅n, m⁆ ∈ F Finset.univ at this
        rwa [h, Subgroup.mem_bot] at this
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    · exact h
  have hex : ∃ k, ∃ A : Finset ι, A.card = k ∧ F A = ⊤ := ⟨_, Finset.univ, rfl, hFuniv⟩
  obtain ⟨A, hAk, hA⟩ := Nat.find_spec hex
  have hmin : ∀ B : Finset ι, B.card < A.card → F B = ⊥ := fun B hB =>
    (hFbot_or_top B).resolve_right fun hB' => Nat.find_min hex (hAk ▸ hB) ⟨B, rfl, hB'⟩
  have hTnt : (⊥ : Subgroup T) ≠ ⊤ := by
    intro h
    exact hTc fun a b => by
      have ha : a ∈ (⊥ : Subgroup T) := h ▸ Subgroup.mem_top a
      have hb : b ∈ (⊥ : Subgroup T) := h ▸ Subgroup.mem_top b
      rw [Subgroup.mem_bot] at ha hb
      rw [ha, hb]
  have hF0 : F ∅ = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨n, hn, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, LeviBlock.mem_normalSupp] at hn
    have : n = 1 := Subtype.ext (funext fun i => hn.2.2 i (Finset.notMem_empty i))
    rw [this, map_one]
    exact Subgroup.one_mem _
  obtain ⟨j, hj⟩ : A.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    exact hTnt (hF0.symm.trans hA)
  have hFe : F (A.erase j) = ⊥ := hmin _ (Finset.card_erase_lt_of_mem hj)
  set NA := LeviBlock.normalSupp N S A with hNA
  have hNAN : NA ≤ N := fun x hx => (LeviBlock.mem_normalSupp.mp hx).1
  let π : ↥NA →* ↥(S j) :=
    { toFun := fun n => ⟨(n : ∀ i, G i) j, (LeviBlock.mem_normalSupp.mp n.2).2.1 j⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hπ : ∀ n : ↥NA, ((π n : ↥(S j)) : G j) = (n : ∀ i, G i) j := fun _ => rfl
  let fA : ↥NA →* T := f.comp (Subgroup.inclusion hNAN)
  have hfA : Function.Surjective fA := by
    intro t
    have ht : t ∈ F A := hA ▸ Subgroup.mem_top t
    obtain ⟨n, hn, rfl⟩ := ht
    exact ⟨⟨n, Subgroup.mem_subgroupOf.mp hn⟩, rfl⟩
  have hker : π.rangeRestrict.ker ≤ fA.ker := by
    intro n hn
    rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker] at hn
    have hnj : (n : ∀ i, G i) j = 1 := by
      have := congrArg Subtype.val hn
      rwa [hπ] at this
    have hmem : Subgroup.inclusion hNAN n ∈
        (LeviBlock.normalSupp N S (A.erase j)).subgroupOf N := by
      rw [Subgroup.mem_subgroupOf, LeviBlock.mem_normalSupp]
      obtain ⟨h1, h2, h3⟩ := LeviBlock.mem_normalSupp.mp n.2
      refine ⟨h1, h2, fun i hi => ?_⟩
      by_cases hij : i = j
      · subst hij; exact hnj
      · exact h3 i fun hiA => hi (Finset.mem_erase.mpr ⟨hij, hiA⟩)
    have := Subgroup.mem_map_of_mem f hmem
    change fA n ∈ F (A.erase j) at this
    rw [hFe, Subgroup.mem_bot] at this
    exact this
  set g : ↥π.range →* T :=
    π.rangeRestrict.liftOfSurjective π.rangeRestrict_surjective ⟨fA, hker⟩ with hgd
  have hgπ : ∀ n, g (π.rangeRestrict n) = fA n := fun n => by simp [hgd]
  have hg : Function.Surjective g := fun t => by
    obtain ⟨n, rfl⟩ := hfA t
    exact ⟨π.rangeRestrict n, hgπ n⟩
  have hRn : π.range.Normal := ⟨fun v hv s => by
    obtain ⟨n, rfl⟩ := hv
    set e : ∀ i, G i := Pi.mulSingle j (s : G j) with he
    have heS : e ∈ Subgroup.pi Set.univ S := (Subgroup.mem_pi _).mpr fun i _ => by
      by_cases h : i = j
      · subst h; rw [he, Pi.mulSingle_eq_same]; exact s.2
      · rw [he, Pi.mulSingle_eq_of_ne h]; exact Subgroup.one_mem _
    obtain ⟨h1, h2, h3⟩ := LeviBlock.mem_normalSupp.mp n.2
    have hm : e * (n : ∀ i, G i) * e⁻¹ ∈ NA := by
      refine LeviBlock.mem_normalSupp.mpr
        ⟨(Subgroup.mem_normalizer_iff.mp (hN (hSX heS)) _).mp h1, fun i => ?_, fun i hi => ?_⟩
      · exact (Subgroup.mem_pi _).mp
          (hconj _ (hSX heS) _ ((Subgroup.mem_pi _).mpr fun i _ => h2 i)) i
          (Set.mem_univ i)
      · simp [Pi.mul_apply, Pi.inv_apply, h3 i hi]
    refine ⟨⟨_, hm⟩, Subtype.ext ?_⟩
    rw [hπ]
    simp [he, Pi.mul_apply, Pi.inv_apply, Pi.mulSingle_eq_same, hπ]⟩
  rcases hS j with hq | hsol
  · rcases CFSG.AGLEmbedding.le_center_or_eq_top_of_normal_quasisimple hq π.range with hc | htop
    · exfalso
      refine hTc fun a b => ?_
      obtain ⟨v, rfl⟩ := hg a
      obtain ⟨w, rfl⟩ := hg b
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_center_iff.mp (hc v.2) w).symm
    · have hmulS : ∀ s ∈ S j, (Pi.mulSingle j s : ∀ i, G i) ∈ N := by
        have hcomm' : commutator ↥(S j) ≤
            N.comap ((MonoidHom.mulSingle G j).comp (S j).subtype) := by
          rw [commutator_def, Subgroup.commutator_le]
          intro a _ b _
          obtain ⟨n, hn⟩ := (htop ▸ Subgroup.mem_top a : a ∈ π.range)
          have hnj : (n : ∀ i, G i) j = (a : G j) := by rw [← hπ n, hn]
          have hbX : (Pi.mulSingle j (b : G j) : ∀ i, G i) ∈ X :=
            hSX ((Subgroup.mem_pi _).mpr fun i _ => by
              by_cases h : i = j
              · subst h; rw [Pi.mulSingle_eq_same]; exact b.2
              · rw [Pi.mulSingle_eq_of_ne h]; exact Subgroup.one_mem _)
          have hnN : (n : ∀ i, G i) ∈ N := hNAN n.2
          have hc : ⁅(n : ∀ i, G i), Pi.mulSingle j (b : G j)⁆ ∈ N := by
            rw [commutatorElement_def]
            have h1 : (Pi.mulSingle j (b : G j) : ∀ i, G i) * (n : ∀ i, G i)⁻¹ *
                (Pi.mulSingle j (b : G j))⁻¹ ∈ N :=
              (Subgroup.mem_normalizer_iff.mp (hN hbX) _).mp (N.inv_mem hnN)
            have := N.mul_mem hnN h1
            simpa [mul_assoc] using this
          have heq : ⁅(n : ∀ i, G i), Pi.mulSingle j (b : G j)⁆ =
              Pi.mulSingle j ⁅(a : G j), (b : G j)⁆ := by
            funext i
            by_cases hij : i = j
            · subst hij
              simp only [commutatorElement_def, Pi.mul_apply, Pi.inv_apply,
                Pi.mulSingle_eq_same]
              rw [hnj]
            · simp [commutatorElement_def, Pi.mulSingle_eq_of_ne hij]
          rw [heq] at hc
          change Pi.mulSingle j ((⁅a, b⁆ : ↥(S j)) : G j) ∈ N
          have hab : ((⁅a, b⁆ : ↥(S j)) : G j) = ⁅(a : G j), (b : G j)⁆ := by
            simp [commutatorElement_def]
          rw [hab]
          exact hc
        rw [hq.1] at hcomm'
        intro s hs
        exact (hcomm' (Subgroup.mem_top (⟨s, hs⟩ : ↥(S j))) : (⟨s, hs⟩ : ↥(S j)) ∈ _)
      refine ⟨j, hq, hmulS, ?_, ?_⟩
      ·
        set σ : ↥(S j) →* T :=
          g.comp ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv).symm.toMonoidHom with hσ
        have hσs : Function.Surjective σ := hg.comp (MulEquiv.surjective _)
        have hZT : Subgroup.center T = ⊥ := by
          rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center T) with h | h
          · exact h
          · exact absurd (fun a b => Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a) hTc
        have hkσ : σ.ker = Subgroup.center ↥(S j) := by
          apply le_antisymm
          · rcases CFSG.AGLEmbedding.le_center_or_eq_top_of_normal_quasisimple hq σ.ker with h | h
            · exact h
            · exfalso
              apply hTnt
              rw [eq_top_iff]
              intro t _
              obtain ⟨y, rfl⟩ := hσs t
              rw [Subgroup.mem_bot]
              exact MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top y)
          · intro z hz
            rw [MonoidHom.mem_ker, ← Subgroup.mem_bot, ← hZT, Subgroup.mem_center_iff]
            intro t
            obtain ⟨y, rfl⟩ := hσs t
            rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz y)]
        rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective σ hσs).toEquiv]
        exact Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hkσ).toEquiv
      ·
        intro t
        obtain ⟨v, hv⟩ := hg t
        set s : G j := ((v : ↥(S j)) : G j) with hsd
        have hsS : s ∈ S j := (v : ↥(S j)).2
        have hmN : (Pi.mulSingle j s : ∀ i, G i) ∈ N := hmulS s hsS
        have hmS : ∀ i, (Pi.mulSingle j s : ∀ i, G i) i ∈ S i := fun i => by
          by_cases h : i = j
          · subst h; rw [Pi.mulSingle_eq_same]; exact hsS
          · rw [Pi.mulSingle_eq_of_ne h]; exact Subgroup.one_mem _
        have hmA : ∀ i, i ∉ A → (Pi.mulSingle j s : ∀ i, G i) i = 1 := fun i hi => by
          have : i ≠ j := fun h => hi (h ▸ hj)
          exact Pi.mulSingle_eq_of_ne this _
        let m : ↥NA := ⟨Pi.mulSingle j s, LeviBlock.mem_normalSupp.mpr ⟨hmN, hmS, hmA⟩⟩
        have hπm : π.rangeRestrict m = v := by
          apply Subtype.ext
          apply Subtype.ext
          change ((π m : ↥(S j)) : G j) = s
          rw [hπ]
          simp [m]
        refine ⟨s, hsS, hmN, ?_⟩
        have h1 := hgπ m
        rw [hπm] at h1
        rw [← hv, h1]
        rfl
  · exfalso
    have : Group.IsSolvable ↥(S j) := hsol
    have : Group.IsSolvable T := Group.isSolvable_of_surjective hg
    exact hTc (IsSimpleGroup.comm_iff_isSolvable.mpr this)

theorem exists_two_blocks_of_normal_section [∀ j, Finite (G j)] {S : ∀ j, Subgroup (G j)}
    {X : Subgroup (∀ j, G j)} (hSX : Subgroup.pi Set.univ S ≤ X)
    (hXX : ⁅X, X⁆ ≤ Subgroup.pi Set.univ S)
    (hS : ∀ j, CFSG.Open.IsQuasisimple (S j) ∨ Group.IsSolvable (S j))
    {N : Subgroup (∀ j, G j)} (hNX : N ≤ X)
    (hN : X ≤ Subgroup.normalizer (N : Set (∀ j, G j)))
    {U₁ U₂ : Type} [Group U₁] [Group U₂] [IsSimpleGroup U₁] [IsSimpleGroup U₂]
    (h₁ : ∃ a b : U₁, a * b ≠ b * a) (h₂ : ∃ a b : U₂, a * b ≠ b * a)
    (f : ↥N →* U₁ × U₂) (hf : Function.Surjective f) :
    ∃ j₁ j₂, j₁ ≠ j₂ ∧ CFSG.Open.IsQuasisimple (S j₁) ∧ CFSG.Open.IsQuasisimple (S j₂) ∧
      Nat.card U₁ = Nat.card (↥(S j₁) ⧸ Subgroup.center ↥(S j₁)) ∧
      Nat.card U₂ = Nat.card (↥(S j₂) ⧸ Subgroup.center ↥(S j₂)) := by
  classical
  have hf₁ : Function.Surjective ((MonoidHom.fst U₁ U₂).comp f) := fun a => by
    obtain ⟨n, hn⟩ := hf (a, 1)
    exact ⟨n, by simp [hn]⟩
  have hf₂ : Function.Surjective ((MonoidHom.snd U₁ U₂).comp f) := fun a => by
    obtain ⟨n, hn⟩ := hf (1, a)
    exact ⟨n, by simp [hn]⟩
  obtain ⟨j₁, hq₁, hm₁, hc₁, hs₁⟩ :=
    exists_attached_block_of_normal_section hSX hXX hS hNX hN h₁ _ hf₁
  obtain ⟨j₂, hq₂, hm₂, hc₂, hs₂⟩ :=
    exists_attached_block_of_normal_section hSX hXX hS hNX hN h₂ _ hf₂
  refine ⟨j₁, j₂, ?_, hq₁, hq₂, hc₁, hc₂⟩
  intro hj
  subst hj
  let θ : ↥(S j₁) →* ↥N :=
    ((MonoidHom.mulSingle G j₁).comp (S j₁).subtype).codRestrict N fun s => hm₁ s.1 s.2
  let σ : ↥(S j₁) →* U₁ × U₂ := f.comp θ
  have hconj : ∀ x ∈ X, ∀ m ∈ Subgroup.pi Set.univ S, x * m * x⁻¹ ∈ Subgroup.pi Set.univ S := by
    intro x hx m hm
    have e : x * m * x⁻¹ = ⁅x, m⁆ * m := by rw [commutatorElement_def]; group
    rw [e]
    exact Subgroup.mul_mem _ (hXX (Subgroup.commutator_mem_commutator hx (hSX hm))) hm
  have hWn : σ.range.Normal := by
    refine ⟨fun w hw g => ?_⟩
    obtain ⟨s, rfl⟩ := hw
    obtain ⟨n, rfl⟩ := hf g
    set x : ∀ i, G i := (n : ∀ i, G i) with hx
    have hxX : x ∈ X := hNX n.2
    have hmP : (Pi.mulSingle j₁ (s : G j₁) : ∀ i, G i) ∈ Subgroup.pi Set.univ S :=
      (Subgroup.mem_pi _).mpr fun i _ => by
        by_cases h : i = j₁
        · subst h; rw [Pi.mulSingle_eq_same]; exact s.2
        · rw [Pi.mulSingle_eq_of_ne h]; exact Subgroup.one_mem _
    have hconjP := (Subgroup.mem_pi _).mp (hconj x hxX _ hmP) j₁ (Set.mem_univ j₁)
    have heq : x * Pi.mulSingle j₁ (s : G j₁) * x⁻¹ =
        Pi.mulSingle j₁ (x j₁ * (s : G j₁) * (x j₁)⁻¹) := by
      funext i
      by_cases hij : i = j₁
      · subst hij
        simp
      · simp [Pi.mulSingle_eq_of_ne hij]
    have hs' : x j₁ * (s : G j₁) * (x j₁)⁻¹ ∈ S j₁ := by
      have : (x * Pi.mulSingle j₁ (s : G j₁) * x⁻¹) j₁ = x j₁ * (s : G j₁) * (x j₁)⁻¹ := by
        rw [heq]; simp
      rw [← this]
      exact hconjP
    refine ⟨⟨x j₁ * (s : G j₁) * (x j₁)⁻¹, hs'⟩, ?_⟩
    change f (θ ⟨x j₁ * (s : G j₁) * (x j₁)⁻¹, hs'⟩) = f n * f (θ s) * (f n)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact heq.symm
  have hW₁ : ∀ u : U₁, ∃ w ∈ σ.range, w.1 = u := fun u => by
    obtain ⟨s, hs, hsN, h⟩ := hs₁ u
    exact ⟨σ ⟨s, hs⟩, ⟨⟨s, hs⟩, rfl⟩, h⟩
  have hW₂ : ∀ u : U₂, ∃ w ∈ σ.range, w.2 = u := fun u => by
    obtain ⟨s, hs, hsN, h⟩ := hs₂ u
    exact ⟨σ ⟨s, hs⟩, ⟨⟨s, hs⟩, rfl⟩, h⟩
  haveI := hWn
  have htop := eq_top_of_normal_of_proj_surjective h₁ h₂ hW₁ hW₂
  exact not_exists_surjective_quasisimple_prod h₁ h₂ hq₁ σ (MonoidHom.range_eq_top.mp htop)

end NormalSection

section Cover

variable {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type} [∀ j, Group (G j)]
  [∀ j, Finite (G j)]

theorem exists_two_blocks_of_hom {Q : Type} [Group Q] {S : ∀ j, Subgroup (G j)}
    (β : Q →* ∀ j, G j) (hker : IsPGroup 2 β.ker) (hpi : Subgroup.pi Set.univ S ≤ β.range)
    (hcomm : ⁅β.range, β.range⁆ ≤ Subgroup.pi Set.univ S)
    (hS : ∀ j, CFSG.Open.IsQuasisimple (S j) ∨ Group.IsSolvable (S j))
    {Ñ : Subgroup Q} [hÑ : Ñ.Normal] {U₁ U₂ : Type} [Group U₁] [Group U₂] [Finite U₁]
    [Finite U₂] [IsSimpleGroup U₁] [IsSimpleGroup U₂] (h₁ : ∃ a b : U₁, a * b ≠ b * a)
    (h₂ : ∃ a b : U₂, a * b ≠ b * a) (h3₁ : 3 ∣ Nat.card U₁) (h3₂ : 3 ∣ Nat.card U₂)
    (f : ↥Ñ →* U₁ × U₂) (hf : Function.Surjective f) :
    ∃ j₁ j₂, j₁ ≠ j₂ ∧ CFSG.Open.IsQuasisimple (S j₁) ∧ CFSG.Open.IsQuasisimple (S j₂) ∧
      Nat.card U₁ = Nat.card (↥(S j₁) ⧸ Subgroup.center ↥(S j₁)) ∧
      Nat.card U₂ = Nat.card (↥(S j₂) ⧸ Subgroup.center ↥(S j₂)) := by
  have hf₁ : Function.Surjective ((MonoidHom.fst U₁ U₂).comp f) := fun a => by
    obtain ⟨n, hn⟩ := hf (a, 1)
    exact ⟨n, by simp [hn]⟩
  have hf₂ : Function.Surjective ((MonoidHom.snd U₁ U₂).comp f) := fun a => by
    obtain ⟨n, hn⟩ := hf (1, a)
    exact ⟨n, by simp [hn]⟩
  set βN : ↥Ñ →* ↥(Ñ.map β) := (β.comp Ñ.subtype).codRestrict (Ñ.map β)
    (fun n => ⟨n, n.2, rfl⟩) with hβN
  have hβNs : Function.Surjective βN := by
    rintro ⟨_, ⟨n, hn, rfl⟩⟩
    exact ⟨⟨n, hn⟩, rfl⟩
  have hk : βN.ker ≤ f.ker := by
    have h2 : IsPGroup 2 βN.ker := by
      intro n
      have hn : (n : ↥Ñ).1 ∈ β.ker := by
        have := congrArg Subtype.val (MonoidHom.mem_ker.mp n.2)
        exact MonoidHom.mem_ker.mpr this
      obtain ⟨e, he⟩ := hker ⟨_, hn⟩
      refine ⟨e, Subtype.ext (Subtype.ext ?_)⟩
      have := congrArg Subtype.val he
      simpa using this
    intro x hx
    have a1 := LeviBlock.le_ker_of_isPGroup_two h3₁ ((MonoidHom.fst U₁ U₂).comp f) hf₁
      (K := βN.ker) h2 hx
    have a2 := LeviBlock.le_ker_of_isPGroup_two h3₂ ((MonoidHom.snd U₁ U₂).comp f) hf₂
      (K := βN.ker) h2 hx
    exact Prod.ext a1 a2
  obtain ⟨f', hf', -⟩ := LeviBlock.exists_factor βN hβNs f hf hk
  have hNX : Ñ.map β ≤ β.range := Subgroup.map_le_range β Ñ
  have hNn' : β.range ≤ Subgroup.normalizer ((Ñ.map β : Subgroup _) : Set _) := by
    rintro _ ⟨q, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨q * n * q⁻¹, hÑ.conj_mem n hn q, by simp⟩
    · intro hy
      obtain ⟨n, hn, hne⟩ := hy
      refine ⟨q⁻¹ * n * q, by simpa using hÑ.conj_mem n hn q⁻¹, ?_⟩
      rw [map_mul, map_mul, hne, map_inv]
      group
  exact exists_two_blocks_of_normal_section hpi hcomm hS hNX hNn' h₁ h₂ f' hf'

theorem two_blocks_of_l28Section {Y : Type} [Group Y] [Finite Y] {L P : Subgroup Y} (hPL : P ≤ L)
    {K : Type} [Group K] (ρ : K →* ↥L) (hρ : Function.Surjective ρ) {S : ∀ j, Subgroup (G j)}
    (β : ↥((P.subgroupOf L).comap ρ) →* ∀ j, G j) (hker : IsPGroup 2 β.ker)
    (hpi : Subgroup.pi Set.univ S ≤ β.range) (hcomm : ⁅β.range, β.range⁆ ≤ Subgroup.pi Set.univ S)
    (hS : ∀ j, CFSG.Open.IsQuasisimple (S j) ∨ Group.IsSolvable (S j))
    {N : Subgroup Y} (hNP : N ≤ P) (hPN : P ≤ Subgroup.normalizer (N : Set Y))
    {d₁ d₂ : TauCeti.ValidLieTypeIndex} (ψ : ↥N →* CatGroup d₁ × CatGroup d₂)
    (hd₁ : IsCaseTwoIndex 3 d₁) (hd₂ : IsCaseTwoIndex 3 d₂) (hψ : Function.Surjective ψ) :
    ∃ j₁ j₂ : ι, j₁ ≠ j₂ ∧ CFSG.Open.IsQuasisimple (S j₁) ∧ CFSG.Open.IsQuasisimple (S j₂) ∧
      Nat.card (↥(S j₁) ⧸ Subgroup.center ↥(S j₁)) = 504 ∧
      Nat.card (↥(S j₂) ⧸ Subgroup.center ↥(S j₂)) = 504 := by
  have hc₁ : IsCaseTwoGroup 3 (CatGroup d₁) := ⟨d₁, hd₁, ⟨MulEquiv.refl _⟩⟩
  have hc₂ : IsCaseTwoGroup 3 (CatGroup d₂) := ⟨d₂, hd₂, ⟨MulEquiv.refl _⟩⟩
  have : IsSimpleGroup (CatGroup d₁) := isSimpleGroup_of_isCaseTwoGroup_three hc₁
  have : IsSimpleGroup (CatGroup d₂) := isSimpleGroup_of_isCaseTwoGroup_three hc₂
  have : Finite (CatGroup d₁ × CatGroup d₂) := Finite.of_surjective ψ hψ
  have : Finite (CatGroup d₁) :=
    Finite.of_surjective (Prod.fst : CatGroup d₁ × CatGroup d₂ → CatGroup d₁)
      (fun a => ⟨(a, (1 : CatGroup d₂)), rfl⟩)
  have : Finite (CatGroup d₂) :=
    Finite.of_surjective (Prod.snd : CatGroup d₁ × CatGroup d₂ → CatGroup d₂)
      (fun b => ⟨((1 : CatGroup d₁), b), rfl⟩)
  have hcard₁ := card_of_isCaseTwoGroup_three hc₁
  have hcard₂ := card_of_isCaseTwoGroup_three hc₂
  set N' := N.subgroupOf P with hN'd
  have hN'n : N'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNP).mpr hPN
  set ψ' : ↥N' →* CatGroup d₁ × CatGroup d₂ :=
    ψ.comp (Subgroup.subgroupOfEquivOfLe hNP).toMonoidHom with hψ'd
  have hψ' : Function.Surjective ψ' := hψ.comp (MulEquiv.surjective _)
  set ρQ : ↥((P.subgroupOf L).comap ρ) →* ↥P :=
    { toFun := fun q => ⟨((ρ q : ↥L) : Y), Subgroup.mem_subgroupOf.mp q.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp } with hρQ
  have hρQs : Function.Surjective ρQ := by
    rintro ⟨p, hp⟩
    obtain ⟨k, hk⟩ := hρ ⟨p, hPL hp⟩
    refine ⟨⟨k, ?_⟩, ?_⟩
    · show ρ k ∈ P.subgroupOf L
      rw [hk]
      exact Subgroup.mem_subgroupOf.mpr hp
    · ext
      simp [hρQ, hk]
  set Ñ := N'.comap ρQ with hÑd
  haveI : Ñ.Normal := hN'n.comap ρQ
  set g : ↥Ñ →* CatGroup d₁ × CatGroup d₂ := ψ'.comp (ρQ.subgroupComap N') with hg
  have hg' : Function.Surjective g := by
    intro u
    obtain ⟨⟨y, hy⟩, rfl⟩ := hψ' u
    obtain ⟨q, rfl⟩ := hρQs y
    exact ⟨⟨q, hy⟩, rfl⟩
  obtain ⟨j₁, j₂, hne, hq₁, hq₂, h₁, h₂⟩ := exists_two_blocks_of_hom β hker hpi hcomm hS
    (ThreeFives.exists_noncomm_of_simple inferInstance (by rw [hcard₁]; norm_num))
    (ThreeFives.exists_noncomm_of_simple inferInstance (by rw [hcard₂]; norm_num))
    (by rw [hcard₁]; norm_num) (by rw [hcard₂]; norm_num) g hg'
  exact ⟨j₁, j₂, hne, hq₁, hq₂, h₁.symm.trans hcard₁, h₂.symm.trans hcard₂⟩

end Cover


end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
