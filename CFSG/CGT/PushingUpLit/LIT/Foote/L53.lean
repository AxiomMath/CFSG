module

public import CFSG.CGT.PushingUpLit.LIT.Foote.L53B
public import CFSG.CGT.PushingUpLit.LIT.Foote.ZSub

public section

namespace CFSG.CGT.PushingUpLit.LIT.Foote

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUp CFSG.Assembly
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.CGT.PushingUpLit.LIT.Foote (QBlock)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace CE

variable {M J : Subgroup G} (c : CE G M J)
include c

theorem lemma_5_3 (hA : FooteTheoremA) {z₀ : G} (hz₀ : ZData J z₀) {W : Subgroup G}
    (hWM : W ≤ M) (hW : CFSG.Open.IsElemAbelian 2 W) (hW4 : Nat.card W = 4) {g : G} (hg : g ∉ M)
    (hC : ∀ w ∈ W, w ≠ 1 → Subgroup.centralizer ({w} : Set G) ≤ rightConjugate M g) :
    W ≤ Subgroup.normalizer (J : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hnot
  obtain ⟨x, hxW, hxN⟩ := Set.not_subset.1 hnot
  set Ω := rightConjugate M g with hΩ
  have hJ := c.block
  have hW2 : ∀ w ∈ W, w * w = 1 := fun w hw => by simpa [pow_two] using hW.2 w hw
  have hWc : ∀ w ∈ W, ∀ w' ∈ W, w * w' = w' * w := fun w hw w' hw' => by
    have := hW.1
    exact setLike_mul_comm hw hw'
  have hx1 : x ≠ 1 := fun h => hxN (h ▸ Subgroup.one_mem _)
  have hxM : x ∈ M := hWM hxW
  have hxne : rightConjugate J x ≠ J := fun h => hxN ((rightConjugate_eq_self_iff J x).1 h)
  have hJΩ : ¬ J ≤ Ω := by
    intro hle
    apply hg
    have : rightConjugate J g⁻¹ ≤ M := by
      intro y hy
      rw [mem_rightConjugate_iff] at hy
      have h1 : g⁻¹ * y * g⁻¹⁻¹ ∈ Ω := hle hy
      rw [hΩ, mem_rightConjugate_iff] at h1
      have e : g * (g⁻¹ * y * g⁻¹⁻¹) * g⁻¹ = y := by group
      rwa [e] at h1
    simpa using M.inv_mem (c.mem_of_conj_le this)
  have hy : ∃ y ∈ W, y ≠ 1 ∧ y ∈ Subgroup.normalizer (J : Set G) := by
    by_contra hall
    push Not at hall
    obtain ⟨u, hu, v, hv, hu1, hv1, huv⟩ := exists_two_ne_one (W := W) (by omega)
    exact hJΩ (c.le_of_forall_move hWM hW2 hWc hu hv hu1 hv1 huv hC fun w hw hw1 h =>
      hall w hw hw1 ((rightConjugate_eq_self_iff J w).1 h))
  obtain ⟨y, hyW, hy1, hyN⟩ := hy
  have hyΩ : y ∈ Ω := hC y hyW hy1 (Subgroup.mem_centralizer_singleton_iff.2 rfl)
  have hxΩ : x ∈ Ω := hC x hxW hx1 (Subgroup.mem_centralizer_singleton_iff.2 rfl)
  have hx2 := hW2 x hxW
  have hcom := c.commute_conj_x hxM hxne
  have hΔ : ∀ j ∈ J, j * (x⁻¹ * j * x) ∈ Ω := by
    intro j hj
    apply hC x hxW hx1
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
    have h1 := hcom j hj j hj
    rw [hxi] at h1 ⊢
    calc j * (x * j * x) * x = j * x * j * (x * x) := by group
      _ = j * x * j := by rw [hx2, mul_one]
      _ = (x * x) * j * x * j := by rw [hx2, one_mul]
      _ = x * ((x * j * x) * j) := by group
      _ = x * (j * (x * j * x)) := by rw [← h1]
  have hyy : y * y ∈ Subgroup.centralizer (blockU J : Set G) := by
    rw [hW2 y hyW]
    exact Subgroup.one_mem _
  obtain ⟨a, haV, hay, k, hk, hak⟩ := hA G J hJ y hyN
    ⟨1, by rw [pow_one, pow_two]; exact hW2 y hyW⟩ hyy
  set C : Subgroup G := J ⊓ Subgroup.centralizer ({y} : Set G) with hCdef
  set A₀ : Subgroup G := ⁅C, J⁆ with hA₀
  have haJ : a ∈ J := blockU_le J haV
  have haC : a ∈ C := ⟨haJ, Subgroup.mem_centralizer_singleton_iff.2 hay⟩
  have hA₀Ω : A₀ ≤ Ω := by
    refine Subgroup.commutator_le.2 fun c' hc' j hj => ?_
    have hc'J : c' ∈ J := (Subgroup.mem_inf.1 hc').1
    have hc'Ω : c' ∈ Ω := hC y hyW hy1 (Subgroup.mem_inf.1 hc').2
    have hδ := hΔ j hj
    have e : ⁅c', j * (x⁻¹ * j * x)⁆ = ⁅c', j⁆ := by
      rw [commutatorElement_mul_right_eq_mul_conj,
        commutatorElement_eq_one_iff_mul_comm.2 (hcom c' hc'J j hj)]
      simp
    rw [← e, commutatorElement_def]
    exact Ω.mul_mem (Ω.mul_mem (Ω.mul_mem hc'Ω hδ) (Ω.inv_mem hc'Ω)) (Ω.inv_mem hδ)
  have hCJ : C ≤ J := inf_le_left
  have hA₀J : A₀ ≤ J := by
    rw [hA₀, Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.1 (hCJ.trans Subgroup.le_normalizer)
  have hJA₀ : J ≤ Subgroup.normalizer (A₀ : Set G) := Subgroup.normalizer_commutator_ge_right C J
  have hA₀nc : ¬ A₀ ≤ Subgroup.centralizer (J : Set G) := by
    intro h0
    have h1 : ⁅A₀, J⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 h0
    have h2 : ⁅⁅J, C⁆, J⁆ = ⊥ := by
      rw [Subgroup.commutator_comm J C]
      exact h1
    have h3 : ⁅⁅J, J⁆, C⁆ = ⊥ :=
      Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := J) (H₂ := J) (H₃ := C) h2 h1
    rw [hJ.perfect, Subgroup.commutator_comm] at h3
    have h4 : C ≤ Subgroup.centralizer (J : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 h3
    exact hak (Subgroup.mem_centralizer_iff.1 (h4 haC) k hk).symm
  have hVA₀ : blockU J ≤ A₀ := hJ.blockU_le_of_normal hA₀J hJA₀ hA₀nc
  have hVΩ : blockU J ≤ Ω := hVA₀.trans hA₀Ω
  set V := blockU J with hV
  set Vx := rightConjugate V x with hVx
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hxiΩ : x⁻¹ ∈ Ω := Ω.inv_mem hxΩ
  have hVxΩ : Vx ≤ Ω := by
    intro y' hy'
    rw [hVx, mem_rightConjugate_iff] at hy'
    have h1 : x * y' * x⁻¹ ∈ Ω := hVΩ hy'
    have := Ω.mul_mem (Ω.mul_mem hxiΩ h1) hxΩ
    simpa [mul_assoc] using this
  have hVpg : IsPGroup 2 V := hJ.isPGroup_blockU
  have hVxpg : IsPGroup 2 Vx := hVpg.map _
  have hVxV : Vx ≤ Subgroup.normalizer (V : Set G) := by
    intro y' hy'
    rw [hVx, mem_rightConjugate_iff] at hy'
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun v hv => ?_)
    have := hcom v (blockU_le J hv) (x * y' * x⁻¹) (blockU_le J hy')
    have e : x⁻¹ * (x * y' * x⁻¹) * x = y' := by group
    rwa [e] at this
  have hEpg : IsPGroup 2 (V ⊔ Vx : Subgroup G) := hVpg.to_sup_of_normal_left' hVxpg hVxV
  have hxE : x ∈ Subgroup.normalizer ((V ⊔ Vx : Subgroup G) : Set G) := by
    rw [← rightConjugate_eq_self_iff]
    unfold rightConjugate
    rw [Subgroup.map_sup]
    have h1 : Vx.map (MulAut.conj x⁻¹).toMonoidHom = V := by
      have := rightConjugate_mul V x x
      rw [hx2, rightConjugate_one] at this
      exact this
    rw [h1, sup_comm]
    rfl
  have hxpg : IsPGroup 2 (Subgroup.zpowers x) := CE.isPGroup_zpowers_of_sq hx2 hx1
  have hPpg : IsPGroup 2 ((V ⊔ Vx) ⊔ Subgroup.zpowers x : Subgroup G) :=
    hEpg.to_sup_of_normal_left' hxpg (Subgroup.zpowers_le.2 hxE)
  have hPΩ : (V ⊔ Vx) ⊔ Subgroup.zpowers x ≤ Ω :=
    sup_le (sup_le hVΩ hVxΩ) (Subgroup.zpowers_le.2 hxΩ)
  set Zg := rightConjugate (zSub M z₀) g with hZg
  have hZpg : IsPGroup 2 Zg := c.isPGroup_zg hz₀ g
  have hZ0 : Zg ≠ ⊥ := by
    intro h
    apply zSub_ne_bot hz₀
    have : rightConjugate (zSub M z₀) g = rightConjugate (⊥ : Subgroup G) g := by
      rw [← hZg, h]
      simp [rightConjugate]
    exact rightConjugate_inj'.1 this
  have hZΩ : Ω ≤ Subgroup.normalizer (Zg : Set G) := normalizer_zg g
  have hPZ : (V ⊔ Vx) ⊔ Subgroup.zpowers x ≤ Subgroup.normalizer (Zg : Set G) := hPΩ.trans hZΩ
  have hne := SignalizerFunctorTheorem.Glauberman.Steps678.inf_centralizer_ne_bot Nat.prime_two
    hPpg hZpg hZ0 hPZ
  obtain ⟨⟨z, hz⟩, hz1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have hz1 : z ≠ 1 := fun h => hz1' (Subtype.ext h)
  obtain ⟨hzZ, hzP⟩ := Subgroup.mem_inf.1 hz
  have hzV : ∀ v ∈ V, v * z = z * v := fun v hv =>
    Subgroup.mem_centralizer_iff.1 hzP v (Subgroup.mem_sup_left (Subgroup.mem_sup_left hv))
  have hzx : z * x = x * z :=
    (Subgroup.mem_centralizer_iff.1 hzP x (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))).symm
  have hzNV : z ∈ Subgroup.normalizer (V : Set G) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 hzV)
  have hzM : z ∈ M := by
    refine c.normalizer_le hVpg (blockU_ne_bot_of_short hJ.short) M.one_mem ?_ hzNV
    rw [rightConjugate_one]
    exact le_normalizer_blockU J
  have hJz : rightConjugate J z = J := by
    refine c.eq_of_blockU_eq hzM ?_
    rw [blockU_rightConjugate]
    exact (rightConjugate_eq_self_iff V z).2 hzNV
  have hzJ : z ∈ Subgroup.normalizer (J : Set G) := (rightConjugate_eq_self_iff J z).1 hJz
  exact hJΩ (c.endgame hA hxne hxM hzJ hzx hZΩ hzZ hz1
    (fun u hu hu1 => c.centralizer_le_zg hz₀ hu hu1) hΔ)

end CE

end CFSG.CGT.PushingUpLit.LIT.Foote
