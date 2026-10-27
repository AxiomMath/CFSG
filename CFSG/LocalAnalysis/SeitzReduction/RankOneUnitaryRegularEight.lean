module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryRegularCoords
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEight
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryPartition
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryStartNormalizer

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem exists_translation_of_eight_of_card_sylow
    (h : U3Start G L f t T) (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hf : f = 3) :
    ∃ n ∈ normalizer (szA L T t : Set G) ⊓ centralizer (szA₁ (szT₁ L T) : Set G),
      n * t * n⁻¹ ≠ t := by
  classical
  by_contra hno
  push Not at hno
  obtain ⟨E, _, _, _, σ, hEcard, hσ, hfix, u, v, hc, hA₁u⟩ := h.exists_rootCoords_of_card_sylow hS2
  subst hf
  obtain ⟨hNA₁, -, -⟩ := h.partition_of_card_sylow hS2
  have hNT₁ := h.normalizer_szA_le_of_card_sylow hS2
  have hidx := h.relIndex_centralizer_of_card_sylow hS2
  set A := szA L T t with hA
  set A₁ := szA₁ (szT₁ L T) with hA₁
  set T₁ := szT₁ L T with hT₁
  set N := normalizer (A : Set G) with hN
  have : Fintype E := Fintype.ofFinite E
  have hE64 : Nat.card E = 64 := by rw [hEcard]; norm_num
  have hσσ : ∀ x, σ (σ x) = x := fun x => by
    rw [hσ, hσ, ← pow_mul]
    have h1 : x ^ Fintype.card E = x := FiniteField.pow_card x
    rw [← Nat.card_eq_fintype_card, hE64] at h1
    exact h1
  let Zs : AddSubgroup E :=
    { carrier := {x | σ x = x}
      add_mem' := fun {a b} (ha : σ a = a) (hb : σ b = b) => by
        show σ (a + b) = a + b
        rw [map_add, ha, hb]
      zero_mem' := map_zero σ
      neg_mem' := fun {a} (ha : σ a = a) => by
        show σ (-a) = -a
        rw [map_neg, ha] }
  have hZ8 : Nat.card Zs = 8 := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← hfix]
    rfl
  set ι : Zs →+ E := Zs.subtype with hι
  have hιinj : Function.Injective ι := Zs.subtype_injective
  have hNmem : ∀ a : E, σ (a * σ a) = a * σ a := fun a => by rw [map_mul, hσσ, mul_comm]
  let Nm : E → Zs := fun a => ⟨a * σ a, hNmem a⟩
  have hNm : ∀ a, ι (Nm a) = a ^ 9 := fun a => by
    change a * σ a = a ^ 9
    rw [hσ]
    ring
  have hA₁T : ∀ b ∈ A₁, b ∈ T₁ := fun b hb => szA₁_le _ hb
  have hvZ : ∀ b ∈ A₁, σ (v b) = v b := fun b hb =>
    hc.sigma_v_of_u_eq_zero (hA₁T b hb) ((hA₁u b (hA₁T b hb)).mp hb)
  let w : A₁ → Multiplicative Zs := fun b => Multiplicative.ofAdd ⟨v b, hvZ b b.2⟩
  have hwmul : ∀ b b' : A₁, w (b * b') = w b * w b' := fun b b' => by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    change v ((b : G) * b') = v b + v b'
    exact hc.v_mul_of_u_eq_zero (hA₁T b b.2) (hA₁T b' b'.2) ((hA₁u b (hA₁T b b.2)).mp b.2)
  have hwbij : Function.Bijective w := by
    refine ⟨fun b b' hbb => Subtype.ext ?_, fun z => ?_⟩
    · have h1 : v b = v b' := congrArg (fun z : Multiplicative Zs => ((Multiplicative.toAdd z : Zs) : E)) hbb
      exact hc.inj _ (hA₁T b b.2) _ (hA₁T b' b'.2)
        (by rw [(hA₁u b (hA₁T b b.2)).mp b.2, (hA₁u b' (hA₁T b' b'.2)).mp b'.2]) h1
    · have hz : σ ((Multiplicative.toAdd z : Zs) : E) = (Multiplicative.toAdd z : Zs) :=
        (Multiplicative.toAdd z).2
      obtain ⟨y, hyT, hyu, hyv⟩ := hc.surj 0 _ (by
        rw [hz, zero_mul, add_zero]
        exact CharTwo.add_self_eq_zero _)
      have hyA : y ∈ A₁ := (hA₁u y hyT).mpr hyu
      refine ⟨⟨y, hyA⟩, ?_⟩
      apply Multiplicative.toAdd.injective
      exact Subtype.ext hyv
  let c : A₁ ≃* Multiplicative Zs := MulEquiv.ofBijective (MonoidHom.mk' w hwmul) hwbij
  let ψ : N →* MulAut A₁ := A₁.normalizerMonoidHom.comp (inclusion hNA₁)
  let lam : N →* Multiplicative (AddAut Zs) :=
    (MulAutMultiplicative Zs).toMonoidHom.comp ((MulAut.congr c).toMonoidHom.comp ψ)
  have hlam : ∀ (n : N) (b : G) (hb : b ∈ A₁),
      ((Multiplicative.toAdd (lam n) ⟨v b, hvZ b hb⟩ : Zs) : E) = v ((n : G) * b * (n : G)⁻¹) := by
    intro n b hb
    have hcb : c.symm (Multiplicative.ofAdd ⟨v b, hvZ b hb⟩) = ⟨b, hb⟩ := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    change ((Multiplicative.toAdd (c (ψ n (c.symm (Multiplicative.ofAdd ⟨v b, hvZ b hb⟩)))) : Zs) :
      E) = _
    rw [hcb]
    rfl
  have hcompat : ∀ g ∈ lam.range, ∃ φ : AddAut E, ∀ a,
      Multiplicative.toAdd g (Nm a) = Nm (φ a) := by
    rintro _ ⟨n, rfl⟩
    have hnT : (n : G) ∈ normalizer (T₁ : Set G) := hNT₁ n.2
    have hnA₁ : ∀ y ∈ T₁, y ∈ A₁ → (n : G) * y * (n : G)⁻¹ ∈ A₁ := fun y _ hy =>
      (mem_normalizer_iff.mp (hNA₁ n.2) y).mp hy
    have hconjT : ∀ y ∈ T₁, (n : G) * y * (n : G)⁻¹ ∈ T₁ := fun y hy =>
      (mem_normalizer_iff.mp hnT y).mp hy
    obtain ⟨φ, hφ⟩ := hc.exists_addEquiv_conj hnT
      (fun y hy hu => (hA₁u _ (hconjT y hy)).mp (hnA₁ y hy ((hA₁u y hy).mpr hu)))
      (fun y hy hu => (hA₁u y hy).mp (by
        have h1 := (hA₁u _ (hconjT y hy)).mpr hu
        have h2 := (mem_normalizer_iff.mp (hNA₁ n.2) y).mpr h1
        exact h2))
    refine ⟨φ, fun a => ?_⟩
    obtain ⟨y, hyT, rfl⟩ := hc.u_surj a
    have hy2T : y ^ 2 ∈ T₁ := pow_mem hyT 2
    obtain ⟨hy2u, hy2v⟩ := hc.sq hyT
    have hy2A : y ^ 2 ∈ A₁ := (hA₁u _ hy2T).mpr hy2u
    have hNmy : Nm (u y) = ⟨v (y ^ 2), hvZ _ hy2A⟩ := Subtype.ext hy2v.symm
    obtain ⟨hz2u, hz2v⟩ := hc.sq (hconjT y hyT)
    apply Subtype.ext
    rw [hNmy, hlam n _ hy2A]
    change v ((n : G) * y ^ 2 * (n : G)⁻¹) = φ (u y) * σ (φ (u y))
    rw [← hφ y hyT, ← hz2v]
    congr 1
    rw [sq, sq]
    group
  have hdvd21 : Nat.card lam.range ∣ 21 :=
    card_dvd_21_of_norm_equivariant (by rw [hE64]) hZ8 ι hιinj Nm hNm lam.range hcompat
  have hker : lam.ker ≤ (centralizer ({t} : Set G)).subgroupOf N := by
    intro n hn
    rw [MonoidHom.mem_ker] at hn
    have hψ : ψ n = 1 := by
      have h1 : (MulAut.congr c) (ψ n) = 1 := (MulAutMultiplicative Zs).injective (by
        rw [map_one]
        exact hn)
      exact (MulAut.congr c).injective (by rw [h1, map_one])
    have hnC : (n : G) ∈ centralizer (A₁ : Set G) := by
      refine mem_centralizer_iff.mpr fun b hb => ?_
      have h1 := congrArg (fun φ : MulAut A₁ => ((φ ⟨b, hb⟩ : A₁) : G)) hψ
      change (n : G) * b * (n : G)⁻¹ = b at h1
      calc b * (n : G) = (n : G) * b * (n : G)⁻¹ * n := by rw [h1]
        _ = (n : G) * b := by group
    have hnt := hno n (mem_inf.mpr ⟨n.2, hnC⟩)
    rw [mem_subgroupOf, mem_centralizer_singleton_iff]
    calc (n : G) * t = (n : G) * t * (n : G)⁻¹ * n := by group
      _ = t * n := by rw [hnt]
  have h8 : 2 ^ 3 ∣ Nat.card lam.range := by
    rw [← Subgroup.index_ker, ← hidx]
    exact Subgroup.index_dvd_of_le hker
  have := Nat.dvd_trans h8 hdvd21
  norm_num at this

end U3Start

end CFSG.SeitzReduction.RankOne
