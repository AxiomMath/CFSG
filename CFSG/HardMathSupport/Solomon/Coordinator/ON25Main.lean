module

public import CFSG.RankThree.PartTwo.Sec4.T444.ONanItem434SporONanModel
public import CFSG.HardMathSupport.Solomon.Coordinator.ON25Layer
public import CFSG.HardMathSupport.Solomon.Coordinator.ON25Local

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.RankThree.Native.ONTriple Subgroup CFSG.Open
open scoped commutatorElement

theorem on25_not_le_center {Y : Type*} [Group Y] {K : Subgroup Y}
    (hq : CFSG.Open.IsQuasisimple ↥K) [Finite K] (h3 : 3 ∣ Nat.card K) :
    ¬ K ≤ Subgroup.center Y := by
  intro h
  have hcomm : ∀ x y : ↥K, x * y = y * x := fun x y =>
    Subtype.ext (Subgroup.mem_center_iff.1 (h y.2) x)
  have h1 : (⁅(⊤ : Subgroup ↥K), ⊤⁆ : Subgroup ↥K) ≤ ⊥ :=
    Subgroup.commutator_le.2 fun x _ y _ => by
      rw [Subgroup.mem_bot]
      exact commutatorElement_eq_one_iff_mul_comm.2 (hcomm x y)
  have e : (⁅(⊤ : Subgroup ↥K), ⊤⁆ : Subgroup ↥K) = ⊤ := hq.1
  have h2 : (⊤ : Subgroup ↥K) = ⊥ := by
    rw [← e]
    exact le_bot_iff.1 h1
  have h4 : Nat.card K = 1 := by
    rw [← Subgroup.card_top (G := ↥K), h2, Subgroup.card_bot]
  rw [h4] at h3
  omega

section


theorem on25_core {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsQuasisimple Y)
    (q : GM →* Y) (hq : Function.Surjective q) (hker : q.ker ≤ zpowers zG)
    (hcenter : ∀ a : GM, a ∉ zpowers zG → q a ∉ Subgroup.center Y)
    (hKbar : ∀ n : GM,
      CFSG.Open.IsQuasisimple ↥((K0G.map (MulAut.conj n).toMonoidHom).map q) ∧
        IsPGroup 3 (Subgroup.center ↥((K0G.map (MulAut.conj n).toMonoidHom).map q)) ∧
        3 ∣ Nat.card ((K0G.map (MulAut.conj n).toMonoidHom).map q))
    (B : Subgroup Y) (hBc : ∀ x ∈ B, ∀ b ∈ B, x * b * x⁻¹ * b⁻¹ ∈ Subgroup.center Y)
    {A : Subgroup GM} (hA : CFSG.RankThree.PartTwo.Late.IsE27 A) (hAB : A.map q ≤ B) :
    (⊤ : Subgroup Y) ≤ ⨆ (b : Y) (_ : b ∈ B) (_ : b ∉ Subgroup.center Y),
      GLAPLayer 3 (Subgroup.centralizer ({b} : Set Y)) := by
  set H : Subgroup Y := ⨆ (b : Y) (_ : b ∈ B) (_ : b ∉ Subgroup.center Y),
      GLAPLayer 3 (Subgroup.centralizer ({b} : Set Y)) with hH
  have hker' : q.ker ≤ Subgroup.center GM := hker.trans (by rw [center_GM])
  have hlayer : ∀ a ∈ A, a ∉ zpowers zG → ∃ n : GM,
      centralizer {a} = zpowers a ⊔ K0G.map (MulAut.conj n).toMonoidHom ∧
      (K0G.map (MulAut.conj n).toMonoidHom).map q ≤ H := by
    intro a ha haz
    obtain ⟨n, h1, h2⟩ := on25_exists_conj hA ha haz
    obtain ⟨hqs, hZ, h3⟩ := hKbar n
    refine ⟨n, h1, (on25_layer_image q hq hker' h1 hqs hZ h3).trans ?_⟩
    exact le_iSup₂_of_le (q a) (hAB ⟨a, ha, rfl⟩)
      (le_iSup (fun _ : q a ∉ Subgroup.center Y =>
        GLAPLayer 3 (Subgroup.centralizer ({q a} : Set Y))) (hcenter a haz))
  have hnormL : ∀ x ∈ B, ∀ b ∈ B,
      x ∈ Subgroup.normalizer (GLAPLayer 3 (Subgroup.centralizer ({b} : Set Y)) : Set Y) :=
    fun x hx b hb => on25_normalizer_layer 3 (on25_normalizer_centralizer (hBc x hx b hb))
  have hnormH : ∀ x ∈ B, x ∈ Subgroup.normalizer (H : Set Y) := by
    intro x hx
    have hHS : H = ⨆ L ∈ {L : Subgroup Y | ∃ b ∈ B, b ∉ Subgroup.center Y ∧
        L = GLAPLayer 3 (Subgroup.centralizer ({b} : Set Y))}, L := by
      apply le_antisymm
      · refine iSup₂_le fun b hb => iSup_le fun hbc => ?_
        exact le_iSup₂_of_le _ ⟨b, hb, hbc, rfl⟩ le_rfl
      · refine iSup₂_le fun L hL => ?_
        obtain ⟨b, hb, hbc, rfl⟩ := hL
        exact le_iSup₂_of_le b hb
          (le_iSup (fun _ : b ∉ Subgroup.center Y =>
            GLAPLayer 3 (Subgroup.centralizer ({b} : Set Y))) hbc)
    rw [hHS]
    exact i183_mem_normalizer_biSup fun L hL => by
      obtain ⟨b, hb, _, rfl⟩ := hL
      exact hnormL x hx b hb
  have hnonz : ∃ a ∈ A, a ∉ zpowers zG := by
    by_contra hall
    push Not at hall
    have h1 := Subgroup.card_le_of_le (show A ≤ zpowers zG from hall)
    rw [hA.2, on25_card_zG] at h1
    omega
  have htop : H.comap q ⊔ A = ⊤ :=
    CFSG.RankThree.PartTwo.Sec4.Item434SporONan9.eq_top_of_cent_E27 hA (H.comap q ⊔ A)
      (fun a ha haz => by
        obtain ⟨n, h1, h2⟩ := hlayer a ha haz
        rw [h1]
        exact sup_le ((Subgroup.zpowers_le.2 ha).trans le_sup_right)
          (le_sup_of_le_left fun k hk => h2 ⟨k, hk, rfl⟩))
  have hNtop : Subgroup.normalizer (H : Set Y) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨m, rfl⟩ := hq y
    have hm : m ∈ H.comap q ⊔ A := htop ▸ Subgroup.mem_top m
    have hle : H.comap q ⊔ A ≤ (Subgroup.normalizer (H : Set Y)).comap q :=
      sup_le (fun h hh => Subgroup.le_normalizer hh)
        (fun a ha => hnormH _ (hAB ⟨a, ha, rfl⟩))
    exact hle hm
  haveI hnormal : H.Normal :=
    ⟨fun n hn g => (Subgroup.mem_normalizer_iff.1 (hNtop ▸ Subgroup.mem_top g) n).1 hn⟩
  rcases on25_normal_le_center_or_top hY H with hle | htop'
  · exfalso
    obtain ⟨a, ha, haz⟩ := hnonz
    obtain ⟨n, h1, h2⟩ := hlayer a ha haz
    obtain ⟨hqs, hZ, h3⟩ := hKbar n
    exact on25_not_le_center hqs h3 (h2.trans hle)
  · exact htop'.ge

end

end CFSG.HardMathSupport.Solomon.Coordinator
