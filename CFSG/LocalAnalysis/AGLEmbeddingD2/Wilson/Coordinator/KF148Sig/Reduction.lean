module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.Centralizer
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.Defs
public import CFSG.RankThree.PartTwo.Sec14.Item148Res7ProofSig

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig

open Subgroup CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory CFSG.GH74.GLS
  CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14

theorem aschbacherSolvableCore_eq_bot_of_isSimpleGroup {S : Type*} [Group S] [Finite S]
    [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a) : aschbacherSolvableCore 3 S = ⊥ := by
  obtain ⟨hθs, -⟩ := solvable_prime_complement_core_characterization (H := S) Nat.prime_three
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (aschbacherSolvableCore 3 S) with h | h
  · exact h
  · exfalso
    have h2 : Group.IsSolvable ↥(⊤ : Subgroup S) := by rw [← h]; exact hθs
    have h3 : Group.IsSolvable S :=
      Group.isSolvable_of_surjective
        (f := (Subgroup.topEquiv : ↥(⊤ : Subgroup S) ≃* S).toMonoidHom)
        (Subgroup.topEquiv : ↥(⊤ : Subgroup S) ≃* S).surjective
    obtain ⟨a, b, hab⟩ := hna
    exact hab ((IsSimpleGroup.comm_iff_isSolvable).2 h3 a b)

theorem aschbacherSolvableCore_top_eq_bot {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) : aschbacherSolvableCore 3 ↥(⊤ : Subgroup S) = ⊥ := by
  have : IsSimpleGroup ↥(⊤ : Subgroup S) :=
    (Subgroup.topEquiv : ↥(⊤ : Subgroup S) ≃* S).isSimpleGroup
  obtain ⟨a, b, hab⟩ := hna
  exact aschbacherSolvableCore_eq_bot_of_isSimpleGroup
    ⟨⟨a, mem_top a⟩, ⟨b, mem_top b⟩, fun h => hab (congrArg Subtype.val h)⟩

theorem center_eq_bot_of_isSimpleGroup {S : Type*} [Group S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) : center S = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center S) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    have ha : a ∈ center S := by rw [h]; exact mem_top a
    exact hab ((mem_center_iff.1 ha b).symm)

theorem exists_of_inspect {X : Type} [Group X] [Finite X] (hc : center X = ⊥)
    (hodd : ∀ α : MulAut X, Odd (orderOf α) → ∃ g : X, α = MulAut.conj g)
    {P : Subgroup X → Prop} (hP : InspectSig148 X P)
    (hθ : ∀ K' : Subgroup X, P K' → aschbacherSolvableCore 3 K' = ⊥)
    {Γ : Type} [Group Γ] [Finite Γ] {A L K : Subgroup Γ} {e : Γ} (h : Sig148 A L K e)
    (hker : Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) =
      (zpowers e : Set Γ))
    (ψ : L ⧸ aschbacherSolvableCore 3 L ≃* X) :
    ∃ K' : Subgroup X, P K' ∧ Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃* K') := by
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := h.isE27.1.2
  have hAL := h.le_normalizer_L
  have hAK := h.le_normalizer_K
  set ι := innerHom hAL ψ hc hodd hA3 with hι
  set κ := kappa h.le ψ with hκ
  have hιe : ∀ a : A, ι a = 1 ↔ (a : Γ) ∈ zpowers e := by
    intro a
    rw [hι, innerHom_eq_one_iff, ← SetLike.mem_coe, ← hker]
    exact ⟨fun h' => ⟨a.2, h'⟩, fun h' => h'.2⟩
  have he3 : orderOf e = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime (hA3 e h.mem) h.ne_one
  have hcardE : Nat.card ι.range = 9 := by
    have hzA : zpowers e ≤ A := zpowers_le.2 h.mem
    have hker' : ι.ker = (zpowers e).subgroupOf A := by
      ext a
      rw [MonoidHom.mem_ker, mem_subgroupOf, hιe]
    have hk3 : Nat.card ι.ker = 3 := by
      rw [hker', Nat.card_congr (subgroupOfEquivOfLe hzA).toEquiv, Nat.card_zpowers, he3]
    have h1 := Subgroup.card_mul_index ι.ker
    rw [Subgroup.index_ker, hk3, h.isE27.2] at h1
    omega
  have hexpE : ∀ y ∈ ι.range, y ^ 3 = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_pow, show a ^ 3 = 1 from Subtype.ext (by simpa using hA3 a a.2), map_one]
  have hNE : ι.range ≤ normalizer (κ.range : Set X) :=
    range_innerHom_le_normalizer h.le ψ hAL hAK hc hodd hA3
  have hKp : Group.IsPerfect K := h.isPerfect
  have hKbp : Group.IsPerfect κ.range := Group.IsPerfect.range κ
  have hKb1 : κ.range ≠ ⊥ := by
    intro hb
    have hntq := CFSG.LocalCores.isQuasisimple_nontrivial h.isQuasisimple
    have hnt : Nontrivial K := by
      by_contra hn
      rw [not_nontrivial_iff_subsingleton] at hn
      have : Subsingleton (K ⧸ aschbacherSolvableCore 3 K) :=
        (QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 K)).subsingleton
      exact not_nontrivial _ hntq
    have hall : ∀ k : K, k ∈ κ.ker := fun k => by
      rw [MonoidHom.mem_ker]
      have : κ k ∈ κ.range := ⟨k, rfl⟩
      rwa [hb, mem_bot] at this
    have hsk := isSolvable_ker_kappa h.le ψ
    have hsK : Group.IsSolvable K := Group.isSolvable_of_isSolvable_injective
      (f := { toFun := fun k => (⟨k, hall k⟩ : κ.ker), map_one' := rfl, map_mul' := fun _ _ => rfl })
      (fun k k' hkk => congrArg Subtype.val hkk)
    exact Group.IsPerfect.not_isSolvable K hsK
  have hgen : κ.range ≤ ⨆ (y : X) (_ : y ∈ ι.range) (_ : y ≠ 1),
      pPrimeCoreOf 3 (κ.range ⊓ centralizer ({y} : Set X)) := by
    have htop : (⊤ : Subgroup K) ≤ ⨆ (x : Γ) (_ : x ∈ A) (_ : x ∉ zpowers e),
        (pPrimeCoreOf 3 (K ⊓ centralizer ({x} : Set Γ))).subgroupOf K := by
      intro k _
      have hk := h.le_iSup k.2
      have hS : ∀ x : Γ, pPrimeCoreOf 3 (K ⊓ centralizer ({x} : Set Γ)) ≤ K := fun x => by
        intro y hy
        obtain ⟨c, -, rfl⟩ := hy
        exact (mem_inf.1 c.2).1
      have hmap : (⨆ (x : Γ) (_ : x ∈ A) (_ : x ∉ zpowers e),
          (pPrimeCoreOf 3 (K ⊓ centralizer ({x} : Set Γ))).subgroupOf K).map K.subtype =
          ⨆ (x : Γ) (_ : x ∈ A) (_ : x ∉ zpowers e),
            pPrimeCoreOf 3 (K ⊓ centralizer ({x} : Set Γ)) := by
        simp only [Subgroup.map_iSup, subgroupOf_map_subtype, inf_of_le_left (hS _)]
      rw [← hmap] at hk
      obtain ⟨k', hk', hkk⟩ := hk
      rwa [← Subtype.ext hkk]
    refine (le_of_eq (MonoidHom.range_eq_map κ)).trans ((map_mono htop).trans ?_)
    simp only [Subgroup.map_iSup]
    refine iSup_le fun x => iSup_le fun hx => iSup_le fun hxe => ?_
    have hy1 : ι ⟨x, hx⟩ ≠ 1 := fun h1 => hxe ((hιe ⟨x, hx⟩).1 h1)
    exact le_iSup_of_le (ι ⟨x, hx⟩) (le_iSup_of_le ⟨⟨x, hx⟩, rfl⟩ (le_iSup_of_le hy1
      (map_pPrimeCoreOf_le h.le ψ hAL hAK hc hodd hA3 ⟨x, hx⟩)))
  have hPK := hP ι.range κ.range hcardE hexpE hNE hKbp hKb1 hgen
  exact ⟨κ.range, hPK, Proving.nonempty_quotient_aschbacherSolvableCore_equiv_range κ
    (isSolvable_ker_kappa h.le ψ) (coprime_card_ker_kappa h.le ψ) (hθ _ hPK)⟩

end CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig
