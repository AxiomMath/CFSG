module

public import CFSG.Open.Defs
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGroups
import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviCover

public section

namespace CFSG.AGLEmbedding

open scoped commutatorElement

section NormalSection

variable {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type} [∀ j, Group (G j)]

namespace LeviBlock

def normalSupp (N : Subgroup (∀ j, G j)) (S : ∀ j, Subgroup (G j)) (A : Finset ι) :
    Subgroup (∀ j, G j) :=
  N ⊓ Subgroup.pi Set.univ S ⊓ Subgroup.pi (↑A)ᶜ (fun _ => ⊥)

omit [Fintype ι] [DecidableEq ι] in
theorem mem_normalSupp {N : Subgroup (∀ j, G j)} {S : ∀ j, Subgroup (G j)} {A : Finset ι}
    {x : ∀ j, G j} :
    x ∈ normalSupp N S A ↔ x ∈ N ∧ (∀ j, x j ∈ S j) ∧ ∀ j, j ∉ A → x j = 1 := by
  simp [normalSupp, Subgroup.mem_pi, and_assoc]

end LeviBlock

theorem exists_block_of_normal_section [∀ j, Finite (G j)] {S : ∀ j, Subgroup (G j)}
    {X : Subgroup (∀ j, G j)} (hSX : Subgroup.pi Set.univ S ≤ X)
    (hXX : ⁅X, X⁆ ≤ Subgroup.pi Set.univ S)
    (hS : ∀ j, CFSG.Open.IsQuasisimple (S j) ∨ Group.IsSolvable (S j))
    {N : Subgroup (∀ j, G j)} (hNX : N ≤ X)
    (hN : X ≤ Subgroup.normalizer (N : Set (∀ j, G j)))
    {T : Type} [Group T] [IsSimpleGroup T] (hT : ∃ a b : T, a * b ≠ b * a)
    (f : ↥N →* T) (hf : Function.Surjective f) :
    ∃ j, CFSG.Open.IsQuasisimple (S j) ∧
      Nat.card T = Nat.card (↥(S j) ⧸ Subgroup.center ↥(S j)) := by
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
  obtain ⟨g, hg, -⟩ :=
    LeviBlock.exists_factor π.rangeRestrict π.rangeRestrict_surjective fA hfA hker
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
  · refine ⟨j, hq, ?_⟩
    rcases CFSG.AGLEmbedding.le_center_or_eq_top_of_normal_quasisimple hq π.range with hc | htop
    · exfalso
      refine hTc fun a b => ?_
      obtain ⟨v, rfl⟩ := hg a
      obtain ⟨w, rfl⟩ := hg b
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_center_iff.mp (hc v.2) w).symm
    · set σ : ↥(S j) →* T :=
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
  · exfalso
    have : Group.IsSolvable ↥(S j) := hsol
    have : Group.IsSolvable T := Group.isSolvable_of_surjective hg
    exact hTc (IsSimpleGroup.comm_iff_isSolvable.mpr this)

end NormalSection

end CFSG.AGLEmbedding
