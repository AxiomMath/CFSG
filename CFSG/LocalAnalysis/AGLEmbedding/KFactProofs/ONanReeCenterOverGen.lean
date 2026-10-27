module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanReeCenterOverTorus
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanReeCenterOverCommutator
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanReeCenterOverTI

public section

namespace CFSG.AGLEmbedding.ReeCenterOver

open Equiv CFSG.AGLEmbedding.ReeModel CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley

section Generation

variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]
  (hK : Nat.card K = 3 ^ (2 * a + 1))
  {w₀ : WeylGroup ReeTag.G2.tag}
  (hw₀ : ∀ w, (coxeterSystem ReeTag.G2.tag).length w ≤ (coxeterSystem ReeTag.G2.tag).length w₀)

include hK hw₀ in
theorem center_conj_generates (ha : 1 ≤ a) :
    (stdU a K ⊓ Subgroup.centralizer ((stdU a K : Subgroup ↥(ReeTag.G2.reeGamma K a)) :
      Set ↥(ReeTag.G2.reeGamma K a))) ⊔
    (stdU a K ⊓ Subgroup.centralizer ((stdU a K : Subgroup ↥(ReeTag.G2.reeGamma K a)) :
      Set ↥(ReeTag.G2.reeGamma K a))).map
      (MulAut.conj (nElt (a := a) (K := K) hw₀)).toMonoidHom = ⊤ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Z : Subgroup ↥(ReeTag.G2.reeGamma K a) := stdU a K ⊓ Subgroup.centralizer
    ((stdU a K : Subgroup ↥(ReeTag.G2.reeGamma K a)) : Set ↥(ReeTag.G2.reeGamma K a)) with hZ
  set n := nElt (a := a) (K := K) hw₀ with hn
  set Y₀ : Subgroup ↥(ReeTag.G2.reeGamma K a) := Z ⊔ Z.map (MulAut.conj n).toMonoidHom with hY₀
  obtain ⟨hnn, h9, h3⟩ := longest_sq_and_commutator (K := K) hw₀
  have hnn' : n * n = 1 := Subtype.ext hnn
  have hninv : n⁻¹ = n := inv_eq_of_mul_eq_one_right hnn'
  have hcc : ∀ x : ↥(ReeTag.G2.reeGamma K a), MulAut.conj n (MulAut.conj n x) = x := by
    intro x
    rw [MulAut.conj_apply, MulAut.conj_apply]
    calc n * (n * x * n⁻¹) * n⁻¹ = (n * n) * x * (n⁻¹ * n⁻¹) := by group
      _ = x := by rw [hnn', hninv, hnn', one_mul, mul_one]
  have hc_h : ∀ s : Kˣ, MulAut.conj n (hElt (a := a) hK s) = (hElt (a := a) hK s)⁻¹ := fun s =>
    (MulAut.conj_apply _ _).trans (nElt_mul_hElt hK hw₀ s)
  have hZY : Z ≤ Y₀ := le_sup_left
  have hZ'Y : Z.map (MulAut.conj n).toMonoidHom ≤ Y₀ := le_sup_right
  have hnY : ∀ y ∈ Y₀, MulAut.conj n y ∈ Y₀ := by
    have hle : Y₀ ≤ Y₀.comap (MulAut.conj n).toMonoidHom := by
      refine sup_le ?_ ?_
      · intro z hz
        exact Subgroup.mem_comap.2 (hZ'Y (Subgroup.mem_map_of_mem _ hz))
      · rintro _ ⟨z, hz, rfl⟩
        refine Subgroup.mem_comap.2 ?_
        change MulAut.conj n (MulAut.conj n z) ∈ Y₀
        rw [hcc]
        exact hZY hz
    intro y hy
    exact Subgroup.mem_comap.1 (hle hy)
  have hHY : ∀ (s : Kˣ), ∀ y ∈ Y₀, hElt (a := a) hK s * y * (hElt (a := a) hK s)⁻¹ ∈ Y₀ := by
    intro s
    have hle : Y₀ ≤ Y₀.comap (MulAut.conj (hElt (a := a) hK s)).toMonoidHom := by
      refine sup_le ?_ ?_
      · intro z hz
        exact Subgroup.mem_comap.2 (hZY (hElt_conj_mem_center hK hz))
      · rintro _ ⟨z, hz, rfl⟩
        refine Subgroup.mem_comap.2 ?_
        have hz' : (hElt (a := a) hK s)⁻¹ * z * hElt (a := a) hK s ∈ Z := by
          have := hElt_conj_mem_center hK (s := s⁻¹) hz
          rwa [← hElt_inv hK s, inv_inv] at this
        have e : MulAut.conj n ((hElt (a := a) hK s)⁻¹ * z * hElt (a := a) hK s) =
            hElt (a := a) hK s * MulAut.conj n z * (hElt (a := a) hK s)⁻¹ := by
          rw [map_mul, map_mul, map_inv, hc_h s, inv_inv]
        change hElt (a := a) hK s * MulAut.conj n z * (hElt (a := a) hK s)⁻¹ ∈ Y₀
        rw [← e]
        exact hZ'Y (Subgroup.mem_map_of_mem _ hz')
    intro y hy
    exact Subgroup.mem_comap.1 (hle hy)
  set u₀ : ↥(ReeTag.G2.reeGamma K a) := zHom hK (Multiplicative.ofAdd 1) with hu₀
  have hu₀e : (u₀ : ModGL ReeTag.G2.tag K) = ReeTag.g2U₀ K := by
    rw [g2U₀_eq_smallReeCoord (a := a)]
    rfl
  have hu₀Z : u₀ ∈ Z := by rw [hZ, ← zHom_range hK]; exact ⟨_, rfl⟩
  have hu₀1 : u₀ ≠ 1 := by
    intro h
    have := zHom_injective hK (h.trans (map_one (zHom hK)).symm)
    exact one_ne_zero (Multiplicative.ofAdd.injective this)
  have hZ0 : Z ≠ ⊥ := fun h => hu₀1 (by simpa [h] using hu₀Z)
  set g₉ := u₀ * n * u₀⁻¹ * n⁻¹ with hg₉
  have hg₉e : (g₉ : ModGL ReeTag.G2.tag K) = ReeTag.g2U₀ K *
      canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀ * (ReeTag.g2U₀ K)⁻¹ *
      (canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀)⁻¹ := by
    rw [hg₉, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      Subgroup.coe_inv, hu₀e]
    rfl
  have hg₉9 : g₉ ^ 9 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hg₉e]; exact h9)
  have hg₉3 : g₉ ^ 3 ≠ 1 := by
    intro h
    apply h3
    have h' : ((g₉ ^ 3 : ↥(ReeTag.G2.reeGamma K a)) : ModGL ReeTag.G2.tag K) = 1 := by
      rw [h]; rfl
    rw [Subgroup.coe_pow, hg₉e] at h'
    exact h'
  have hg₉Y : g₉ ∈ Y₀ := by
    have h1 : u₀ ∈ Y₀ := hZY hu₀Z
    have h2 : n * u₀⁻¹ * n⁻¹ ∈ Y₀ := hZ'Y (Subgroup.mem_map_of_mem _ (inv_mem hu₀Z))
    have : g₉ = u₀ * (n * u₀⁻¹ * n⁻¹) := by rw [hg₉]; group
    rw [this]
    exact mul_mem h1 h2
  obtain ⟨⟨S, hSU⟩, hNU, -, -⟩ := std_facts hK
  have hTI : ∀ g : ↥(ReeTag.G2.reeGamma K a),
      g ∉ Subgroup.normalizer ((S : Subgroup ↥(ReeTag.G2.reeGamma K a)) :
        Set ↥(ReeTag.G2.reeGamma K a)) →
      (S : Subgroup ↥(ReeTag.G2.reeGamma K a)) ⊓
        (S : Subgroup ↥(ReeTag.G2.reeGamma K a)).map (MulAut.conj g).toMonoidHom = ⊥ := by
    intro g hg
    rw [hSU, hNU] at hg
    rw [hSU]
    exact inf_map_conj_eq_bot hK hg
  have hZS : Z ≤ (S : Subgroup ↥(ReeTag.G2.reeGamma K a)) := by
    rw [hSU]; exact inf_le_left
  obtain ⟨y, hyY, hy⟩ := exists_conj_mem_of_ti S hTI hZ0 hZS hZY hg₉Y
    ⟨2, by rw [show (3 : ℕ) ^ 2 = 9 by norm_num]; exact hg₉9⟩
  set x₀ := y⁻¹ * g₉ * y with hx₀
  have hx₀Y : x₀ ∈ Y₀ := mul_mem (mul_mem (inv_mem hyY) hg₉Y) hyY
  have hx₀U : x₀ ∈ stdU a K := hSU ▸ hy
  have hx₀3 : x₀ ^ 3 ≠ 1 := by
    intro h
    apply hg₉3
    have hx₀' : x₀ = MulAut.conj y⁻¹ g₉ := by rw [hx₀, MulAut.conj_apply, inv_inv]
    rw [hx₀', ← map_pow] at h
    exact (map_eq_one_iff _ (MulEquiv.injective _)).1 h
  set S₀ : Subgroup ↥(ReeTag.G2.reeGamma K a) := stdU a K ⊓ Y₀ with hS₀
  have hinv : ∀ s : Kˣ, ∀ x ∈ S₀, hElt (a := a) hK s * x * (hElt (a := a) hK s)⁻¹ ∈ S₀ := by
    intro s x hx
    refine ⟨?_, hHY s x hx.2⟩
    have hs : hElt (a := a) hK s ∈ Subgroup.normalizer
        ((stdU a K : Subgroup ↥(ReeTag.G2.reeGamma K a)) : Set ↥(ReeTag.G2.reeGamma K a)) :=
      hNU ▸ hElt_mem_stdB hK s
    exact (Subgroup.mem_normalizer_iff.1 hs x).1 hx.1
  have hUY : stdU a K ≤ Y₀ := fun x hx =>
    (eq_stdU_of_invariant hK ha S₀ inf_le_left hinv ⟨hx₀U, hx₀Y⟩ hx₀3 hx).2
  have hconj : ∀ g : ↥(ReeTag.G2.reeGamma K a), ∀ u ∈ stdU a K, g * u * g⁻¹ ∈ Y₀ := by
    intro g u hu
    by_cases hg : g ∈ stdB a K
    · have : g ∈ Subgroup.normalizer
          ((stdU a K : Subgroup ↥(ReeTag.G2.reeGamma K a)) : Set ↥(ReeTag.G2.reeGamma K a)) :=
        hNU ▸ hg
      exact hUY ((Subgroup.mem_normalizer_iff.1 this u).1 hu)
    · obtain ⟨u₁, hu₁, hb⟩ := exists_u_mul_nElt hw₀ hg
      set b := (u₁ * n)⁻¹ * g with hb'
      have hgb : g = u₁ * n * b := by rw [hb']; group
      have hbN : b ∈ Subgroup.normalizer
          ((stdU a K : Subgroup ↥(ReeTag.G2.reeGamma K a)) : Set ↥(ReeTag.G2.reeGamma K a)) :=
        hNU ▸ hb
      have h1 : b * u * b⁻¹ ∈ stdU a K := (Subgroup.mem_normalizer_iff.1 hbN u).1 hu
      have h2 : n * (b * u * b⁻¹) * n⁻¹ ∈ Y₀ := hnY _ (hUY h1)
      have : g * u * g⁻¹ = u₁ * (n * (b * u * b⁻¹) * n⁻¹) * u₁⁻¹ := by rw [hgb]; group
      rw [this]
      exact mul_mem (mul_mem (hUY hu₁) h2) (inv_mem (hUY hu₁))
  rw [eq_top_iff]
  intro x _
  have hgen := ReeTag.ree_normal_positive_generation ReeTag.G2 a K hK
  have hxΓ : (x : ModGL ReeTag.G2.tag K) ∈ Subgroup.closure {x | ∃ g ∈ ReeTag.G2.reeGamma K a,
      ∃ u ∈ ReeTag.G2.reeFixedPosUnipotent K a, g * u * g⁻¹ = x} := by
    rw [hgen]; exact x.2
  have hle : Subgroup.closure {x | ∃ g ∈ ReeTag.G2.reeGamma K a,
      ∃ u ∈ ReeTag.G2.reeFixedPosUnipotent K a, g * u * g⁻¹ = x} ≤
      Y₀.map (ReeTag.G2.reeGamma K a).subtype := by
    rw [Subgroup.closure_le]
    rintro _ ⟨g, hg, u, hu, rfl⟩
    exact ⟨⟨g, hg⟩ * ⟨u, ReeTag.reeFixedPosUnipotent_le_reeGamma hu⟩ * ⟨g, hg⟩⁻¹,
      hconj _ _ (Subgroup.mem_subgroupOf.2 hu), rfl⟩
  obtain ⟨y', hy', hyx⟩ := hle hxΓ
  have : y' = x := Subtype.ext hyx
  rw [← this]
  exact hy'

include hK in
theorem ree_zero_overgroup (ha : 1 ≤ a) (Y : Subgroup ↥(ReeTag.G2.reeGamma K a))
    (hZY : stdU a K ⊓ Subgroup.centralizer ((stdU a K : Subgroup ↥(ReeTag.G2.reeGamma K a)) :
      Set ↥(ReeTag.G2.reeGamma K a)) ≤ Y)
    (hY : ¬ Group.IsSolvable Y) : Y = ⊤ := by
  classical
  obtain ⟨w₀, hw₀, -⟩ := CFSG.LieType.Chevalley.weyl_longest_element ReeTag.G2.tag
  obtain ⟨-, hNU, -, -⟩ := std_facts hK
  set Z : Subgroup ↥(ReeTag.G2.reeGamma K a) := stdU a K ⊓ Subgroup.centralizer
    ((stdU a K : Subgroup ↥(ReeTag.G2.reeGamma K a)) : Set ↥(ReeTag.G2.reeGamma K a)) with hZ
  set n := nElt (a := a) (K := K) hw₀ with hn
  have hgen : Z ⊔ Z.map (MulAut.conj n).toMonoidHom = ⊤ := center_conj_generates hK hw₀ ha
  have : Group.IsSolvable ↥(stdB a K) := isSolvable_stdB
  have hYB : ¬ Y ≤ stdB a K := fun hle => hY (Group.isSolvable_of_isSolvable_injective
    (f := Subgroup.inclusion hle) (Subgroup.inclusion_injective hle))
  obtain ⟨g, hgY, hgB⟩ := IsConcreteLE.not_le_iff_exists.1 hYB
  obtain ⟨u, hu, hb⟩ := exists_u_mul_nElt hw₀ hgB
  set b := (u * n)⁻¹ * g with hb'
  have hgb : g = u * n * b := by rw [hb']; group
  have huZ : ∀ z ∈ Z, u * z * u⁻¹ = z := by
    intro z hz
    have := Subgroup.mem_centralizer_iff.1 hz.2 u hu
    rw [this]
    group
  have hle : Z ⊔ Z.map (MulAut.conj n).toMonoidHom ≤ Y.comap (MulAut.conj u).toMonoidHom := by
    refine sup_le ?_ ?_
    · intro z hz
      refine Subgroup.mem_comap.2 ?_
      change u * z * u⁻¹ ∈ Y
      rw [huZ z hz]
      exact hZY hz
    · rintro _ ⟨z, hz, rfl⟩
      refine Subgroup.mem_comap.2 ?_
      change u * (n * z * n⁻¹) * u⁻¹ ∈ Y
      have hz' : b⁻¹ * z * b ∈ Z := by
        have := conj_mem_inf_centralizer (stdU a K) (b := b⁻¹) (hNU ▸ inv_mem hb) hz
        rwa [inv_inv] at this
      have : u * (n * z * n⁻¹) * u⁻¹ = g * (b⁻¹ * z * b) * g⁻¹ := by rw [hgb]; group
      rw [this]
      exact mul_mem (mul_mem hgY (hZY hz')) (inv_mem hgY)
  rw [eq_top_iff]
  intro x _
  have hx : u⁻¹ * x * u ∈ Z ⊔ Z.map (MulAut.conj n).toMonoidHom := by rw [hgen]; trivial
  have h1 : u * (u⁻¹ * x * u) * u⁻¹ ∈ Y := Subgroup.mem_comap.1 (hle hx)
  have e : u * (u⁻¹ * x * u) * u⁻¹ = x := by group
  rwa [e] at h1

end Generation

end CFSG.AGLEmbedding.ReeCenterOver
