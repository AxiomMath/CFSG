module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBFusion2
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBFusion1

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42 CFSG.ComponentClassification.J2Cover CFSG.Sporadic.Schreier

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

namespace EndB.JLayer

variable {hs : Setting46e t L p f S w z V i j}
  {π : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) →* P}

theorem mem_centralizer_of_comm (hJ : JLayer hs π)
    {e : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))}
    {q : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)}
    (hq : q ∈ pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
    {y : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))} (hy : y * e = e * y) :
    (y : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ∈
      centralizer {(e : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) * q} := by
  rw [mem_centralizer_singleton_iff]
  rw [← hs.centralizer_layer_eq hJ.h412] at hq
  have hqy : (y : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) * q = q * y :=
    mem_centralizer_iff.mp hq y y.2
  have hye : (y : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) * e = e * y :=
    congrArg Subtype.val hy
  calc (y : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) * (e * q) = (y * e) * q := by group
    _ = (e * y) * q := by rw [hye]
    _ = e * (y * q) := by group
    _ = e * (q * y) := by rw [hqy]
    _ = (e : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) * q * y := by group

theorem not_isPGroup_bar
    (hJ : JLayer hs π) {e : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))}
    {q : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)}
    (hq : q ∈ pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) (he2 : orderOf (π e) = 2) :
    ¬ IsPGroup 2 (Bar (centralizer
      {(e : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) * q})) := by
  have hx : ((π e : P) : Equiv.Perm (Fin 315)) ∈ P := (π e).2
  have hx2 : orderOf ((π e : P) : Equiv.Perm (Fin 315)) = 2 := by
    rw [Subgroup.orderOf_coe, he2]
  have hker : π.ker ≤ center _ := le_of_eq hJ.ker
  rcases inv_cases hx hx2 with ⟨c, hc, hxc, -⟩ | ⟨c, hc, hxc, -⟩
  ·
    obtain ⟨G, hG, hG60, hGp⟩ := exists_perfect_conj hc
    rw [← hxc] at hG
    have hGP : G ≤ P := hG.trans inf_le_left
    have hGperf : Group.IsPerfect ↥G := Subgroup.isPerfect_iff.mpr hGp
    have hAperf : Group.IsPerfect ↥(G.subgroupOf P) :=
      Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hGP).symm.toMonoidHom)
        (subgroupOfEquivOfLe hGP).symm.surjective
    have hAC : G.subgroupOf P ≤ centralizer {π e} := by
      intro a ha
      rw [mem_subgroupOf] at ha
      have h1 := (mem_centralizerIn.mp (hG ha)).2
      exact mem_centralizer_singleton_iff.mpr (Subtype.ext h1)
    obtain ⟨B, hBp, hBC, hBmap⟩ := exists_perfect_lift π hJ.surj hker e hAC
    intro hP
    set ψ : ↥B →* ↥(centralizer {(e : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) * q}) :=
      ((layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).subtype.comp B.subtype).codRestrict _
        (fun b => hJ.mem_centralizer_of_comm hq (mem_centralizer_singleton_iff.mp (hBC b.2)))
      with hψ
    have hrange : ψ.range = ⊥ := by
      have := hBp
      exact eq_bot_of_isPerfect_of_isPGroup_quotient hP (Group.IsPerfect.range ψ)
    have hB : B = ⊥ := by
      rw [eq_bot_iff]
      intro b hb
      have h1 : ψ ⟨b, hb⟩ = 1 := by
        have : ψ ⟨b, hb⟩ ∈ ψ.range := MonoidHom.mem_range.mpr ⟨⟨b, hb⟩, rfl⟩
        rw [hrange] at this
        exact (mem_bot).mp this
      have h2 : (b : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) = 1 :=
        congrArg Subtype.val h1
      exact (mem_bot).mpr (Subtype.ext h2)
    rw [hB, Subgroup.map_bot] at hBmap
    have h1 : Nat.card ↥(G.subgroupOf P) = 60 := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hGP).toEquiv, hG60]
    rw [← hBmap, card_bot] at h1
    omega
  ·
    obtain ⟨o₁, o₂, h1, h2, ho1, ho2, hcl⟩ := exists_odd_gens_c2A
    have hmap := map_conj_centralizerIn P hc permTwoA
    rw [← hxc] at hmap
    have h1' : c * o₁ * c⁻¹ ∈ centralizerIn P ((π e : P) : Equiv.Perm (Fin 315)) := by
      rw [← hmap]; exact ⟨o₁, h1, rfl⟩
    have h2' : c * o₂ * c⁻¹ ∈ centralizerIn P ((π e : P) : Equiv.Perm (Fin 315)) := by
      rw [← hmap]; exact ⟨o₂, h2, rfl⟩
    have hcl' : closure {c * o₁ * c⁻¹, c * o₂ * c⁻¹} =
        centralizerIn P ((π e : P) : Equiv.Perm (Fin 315)) := by
      rw [← map_conj_closure_pair, hcl, hmap]
    set p₁ : P := ⟨c * o₁ * c⁻¹, (mem_centralizerIn.mp h1').1⟩ with hp₁
    set p₂ : P := ⟨c * o₂ * c⁻¹, (mem_centralizerIn.mp h2').1⟩ with hp₂
    have hodd₁ : Odd (orderOf p₁) := by
      rw [hp₁, Subgroup.orderOf_mk, orderOf_conj', ho1]; decide
    have hodd₂ : Odd (orderOf p₂) := by
      rw [hp₂, Subgroup.orderOf_mk, orderOf_conj', ho2]; decide
    have hc₁ : p₁ * π e = π e * p₁ := Subtype.ext (mem_centralizerIn.mp h1').2
    have hc₂ : p₂ * π e = π e * p₂ := Subtype.ext (mem_centralizerIn.mp h2').2
    obtain ⟨y₁, hπy₁, hy₁, hy₁e⟩ := exists_odd_lift π hJ.surj hker hJ.isPGroup_ker hodd₁ hc₁
    obtain ⟨y₂, hπy₂, hy₂, hy₂e⟩ := exists_odd_lift π hJ.surj hker hJ.isPGroup_ker hodd₂ hc₂
    set C := centralizer {(e : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) * q} with hC
    set A : Subgroup ↥C := closure {⟨_, hJ.mem_centralizer_of_comm hq hy₁e⟩,
      ⟨_, hJ.mem_centralizer_of_comm hq hy₂e⟩} with hA
    have hAodd : A ≤ closure {x : ↥C | Odd (orderOf x)} := by
      apply Subgroup.closure_mono
      rintro _ (rfl | rfl)
      · show Odd (orderOf (⟨_, _⟩ : ↥C))
        rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe]; exact hy₁
      · show Odd (orderOf (⟨_, _⟩ : ↥C))
        rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe]; exact hy₂
    have hAE : A.map C.subtype = (closure {y₁, y₂}).map
        (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).subtype := by
      rw [hA, MonoidHom.map_closure, MonoidHom.map_closure, Set.image_pair, Set.image_pair]
      rfl
    have hcardA : Nat.card A = Nat.card (closure ({y₁, y₂} : Set ↥(layer _))) := by
      rw [← Subgroup.card_map_of_injective C.subtype_injective, hAE,
        Subgroup.card_map_of_injective (subtype_injective _)]
    have hπmap : (closure ({y₁, y₂} : Set ↥(layer _))).map π = closure {p₁, p₂} := by
      rw [MonoidHom.map_closure, Set.image_pair, hπy₁, hπy₂]
    have hP1920 : Nat.card ↥(closure ({p₁, p₂} : Set P)) = 1920 := by
      have h := Subgroup.card_map_of_injective (K := closure ({p₁, p₂} : Set P))
        P.subtype_injective
      rw [MonoidHom.map_closure, Set.image_pair] at h
      rw [← h]
      change Nat.card ↥(closure {c * o₁ * c⁻¹, c * o₂ * c⁻¹}) = 1920
      rw [hcl', hxc, card_centralizerIn_conj P hc, inner_classes.2.2.2.2, cent2A_facts.2.1]
    have hA2 : 2 ∣ Nat.card A := by
      rw [hcardA]
      have hdvd := Subgroup.card_map_dvd (closure ({y₁, y₂} : Set ↥(layer _))) π
      rw [hπmap, hP1920] at hdvd
      exact (by norm_num : 2 ∣ 1920).trans hdvd
    exact not_isPGroup_bar_of_odd_gen hAodd hA2

end EndB.JLayer

end CFSG.ComponentClassification.HarrisLit
