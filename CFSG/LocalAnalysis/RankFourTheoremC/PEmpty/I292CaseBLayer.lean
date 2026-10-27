module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28b
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseBStab

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseB

open CFSG.Open Subgroup
open CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement

theorem eq_bot_of_perfect_isPGroup {p : ℕ} [Fact p.Prime] {Y : Type} [Group Y] [Finite Y]
    {J : Subgroup Y} (hJ : ⁅J, J⁆ = J) (hp : IsPGroup p J) : J = ⊥ := by
  haveI : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.2 hJ
  by_contra hne
  haveI : Nontrivial ↥J := (Subgroup.nontrivial_iff_ne_bot J).2 hne
  exact Group.IsPerfect.not_isNilpotent ↥J hp.isNilpotent


theorem glaPLayer_normalizer_eq_bot {p : ℕ} (hp : p.Prime) {Y : Type} [Group Y] [Finite Y]
    {P' : Type} [Group P'] (θ : Y →* MulAut P') (hker : IsPGroup p θ.ker)
    (D : Subgroup (MulAut P')) (hDn : ∀ φ ∈ D, ∀ ψ : MulAut P', ψ * φ * ψ⁻¹ ∈ D)
    (hab : ∀ a b : MulAut P', a * b * a⁻¹ * b⁻¹ ∈ D) (hDθ : D ≤ θ.range)
    (Tb : Subgroup P') {T₀ : Subgroup Y}
    (hX : ∀ y : Y, y ∈ normalizer (T₀ : Set Y) ↔ θ y ∈ stabSub Tb)
    (hA : ∀ φ ψ : MulAut P', φ ∈ D → ψ ∈ D → (∀ t ∈ Tb, φ t = t) → (∀ t ∈ Tb, ψ t = t) →
      φ * ψ = ψ * φ)
    (hB : ∀ φ ∈ D, φ ∈ stabSub Tb →
      (∀ ψ ∈ D, (∀ t ∈ Tb, ψ t = t) → (∃ k : ℕ, ψ ^ (p ^ k) = 1) → φ * ψ = ψ * φ) →
      ∀ t ∈ Tb, φ t = t) :
    GLAPLayer p (normalizer (T₀ : Set Y)) = ⊥ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set X : Subgroup Y := normalizer (T₀ : Set Y) with hXdef
  haveI hDnormal : D.Normal := ⟨fun φ hφ ψ => hDn φ hφ ψ⟩
  let Abar : Subgroup (MulAut P') :=
    { carrier := {φ | φ ∈ D ∧ ∀ t ∈ Tb, φ t = t}
      one_mem' := ⟨D.one_mem, fun t _ => rfl⟩
      mul_mem' := by
        rintro φ ψ ⟨hφD, hφ⟩ ⟨hψD, hψ⟩
        exact ⟨D.mul_mem hφD hψD, fun t ht => by rw [MulAut.mul_apply, hψ t ht, hφ t ht]⟩
      inv_mem' := by
        rintro φ ⟨hφD, hφ⟩
        refine ⟨D.inv_mem hφD, fun t ht => ?_⟩
        calc φ⁻¹ t = φ⁻¹ (φ t) := by rw [hφ t ht]
          _ = t := MulAut.inv_apply_self P' φ t }
  have hAbarcomm : ∀ φ ∈ Abar, ∀ ψ ∈ Abar, φ * ψ = ψ * φ :=
    fun φ hφ ψ hψ => hA φ ψ hφ.1 hψ.1 hφ.2 hψ.2
  let Wbar : Subgroup (MulAut P') :=
    { carrier := {φ | φ ∈ Abar ∧ ∃ k : ℕ, φ ^ (p ^ k) = 1}
      one_mem' := ⟨Abar.one_mem, 0, by simp⟩
      mul_mem' := by
        rintro φ ψ ⟨hφ, i, hi⟩ ⟨hψ, j, hj⟩
        refine ⟨Abar.mul_mem hφ hψ, i + j, ?_⟩
        have hc : Commute φ ψ := hAbarcomm φ hφ ψ hψ
        rw [hc.mul_pow]
        have h1 : φ ^ (p ^ (i + j)) = 1 := by rw [pow_add, pow_mul, hi, one_pow]
        have h2 : ψ ^ (p ^ (i + j)) = 1 := by rw [add_comm, pow_add, pow_mul, hj, one_pow]
        rw [h1, h2, one_mul]
      inv_mem' := by
        rintro φ ⟨hφ, i, hi⟩
        exact ⟨Abar.inv_mem hφ, i, by rw [inv_pow, hi, inv_one]⟩ }
  set W : Subgroup Y := X ⊓ Wbar.comap θ with hW
  have hWX : W ≤ X := inf_le_left
  have hWp : ∀ w ∈ W, ∃ n : ℕ, w ^ (p ^ n) = 1 := by
    intro w hw
    obtain ⟨-, k, hk⟩ := (Subgroup.mem_inf.1 hw).2
    have h1 : w ^ (p ^ k) ∈ θ.ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact hk
    obtain ⟨m, hm⟩ := hker ⟨_, h1⟩
    refine ⟨k + m, ?_⟩
    have : (w ^ (p ^ k)) ^ (p ^ m) = 1 := by simpa using congrArg Subtype.val hm
    rwa [← pow_mul, ← pow_add] at this
  have hWn : ∀ x ∈ X, ∀ w ∈ W, x * w * x⁻¹ ∈ W := by
    intro x hx w hw
    refine Subgroup.mem_inf.2 ⟨X.mul_mem (X.mul_mem hx (hWX hw)) (X.inv_mem hx), ?_⟩
    obtain ⟨⟨hwD, hwfix⟩, k, hk⟩ := (Subgroup.mem_inf.1 hw).2
    have hxst : θ x ∈ stabSub Tb := (hX x).1 hx
    show θ (x * w * x⁻¹) ∈ Wbar
    rw [map_mul, map_mul, map_inv]
    refine ⟨⟨hDn _ hwD _, fun t ht => ?_⟩, k, ?_⟩
    · have hs : (θ x)⁻¹ t ∈ Tb := by
        rw [mem_stabSub.1 hxst, MulAut.apply_inv_self]
        exact ht
      rw [MulAut.mul_apply, MulAut.mul_apply, hwfix _ hs, MulAut.apply_inv_self]
    · rw [conj_pow, hk]
      group
  have hWo : W ≤ oPrimePOf p X := by
    refine Lemma512Ns.le_oPrimePOf_of_core (S₀ := ⊥) hWX ?_ ?_ bot_le ?_ ?_
    · intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro w
      refine ⟨fun h => hWn x hx w h, fun h => ?_⟩
      have := hWn x⁻¹ (X.inv_mem hx) _ h
      simpa [mul_assoc] using this
    · intro x _
      rw [Subgroup.mem_normalizer_iff]
      intro w
      simp only [Subgroup.mem_bot]
      constructor
      · rintro rfl
        simp
      · intro h
        calc w = x⁻¹ * (x * w * x⁻¹) * x := by group
          _ = 1 := by rw [h]; group
    · rw [Subgroup.card_bot]
      exact Nat.coprime_one_right p
    · intro s hs
      obtain ⟨n, hn⟩ := hWp s hs
      exact ⟨n, hn⟩
  refine eq_bot_iff.2 (sSup_le fun J hJ => ?_)
  have hJc : GLAPComponent p X J := hJ
  have hJX : J ≤ X := hJc.1
  have hJperf : ⁅J, J⁆ = J := Lemma53Ns.glaPComponent_perfect hJc
  have hJlayer : J ≤ GLAPLayer p X := le_sSup hJ
  have hcomm : ∀ j ∈ J, ∀ w ∈ W, j * w = w * j := by
    intro j hj w hw
    have h1 : ⁅j, w⁆ ∈ GLAPPrimeCoreOf p X :=
      l28b_commutator_glaPLayer_le hp X
        (Subgroup.commutator_mem_commutator (hJlayer hj) (hWo hw))
    have h2 : ⁅j, w⁆ ∈ W := by
      rw [commutatorElement_def]
      exact W.mul_mem (hWn j (hJX hj) w hw) (W.inv_mem hw)
    obtain ⟨n, hn⟩ := hWp _ h2
    have hcop := CFSG.HardMathSupport.Timmesfeld.Proving.orderOf_coprime_of_mem_GLAPPrimeCoreOf
      hp h1
    have h3 : ⁅j, w⁆ = 1 := by
      have hdvd : orderOf ⁅j, w⁆ ∣ p ^ n := orderOf_dvd_of_pow_eq_one hn
      exact orderOf_eq_one_iff.1
        (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right n hcop) hdvd)
    rw [commutatorElement_def] at h3
    calc j * w = (j * w * j⁻¹ * w⁻¹) * (w * j) := by group
      _ = w * j := by rw [h3, one_mul]
  haveI : (D.comap θ).Normal := Subgroup.normal_comap θ
  have hJD : ⁅J, J⁆ ≤ D.comap θ := by
    refine Subgroup.commutator_le.2 fun a _ b _ => ?_
    show θ ⁅a, b⁆ ∈ D
    rw [commutatorElement_def]
    simp only [map_mul, map_inv]
    exact hab _ _
  rw [hJperf] at hJD
  have hfix : ∀ j ∈ J, ∀ t ∈ Tb, θ j t = t := by
    intro j hj
    refine hB (θ j) (hJD hj) ((hX j).1 (hJX hj)) (fun ψ hψD hψfix hψp => ?_)
    obtain ⟨y, rfl⟩ := hDθ hψD
    have hyst : θ y ∈ stabSub Tb := by
      intro t
      refine ⟨fun ht => by rw [hψfix t ht]; exact ht, fun ht => ?_⟩
      have h1 : (θ y)⁻¹ (θ y t) = θ y t := by
        have hinv : ∀ s ∈ Tb, (θ y)⁻¹ s = s := fun s hs => by
          calc (θ y)⁻¹ s = (θ y)⁻¹ (θ y s) := by rw [hψfix s hs]
            _ = s := MulAut.inv_apply_self P' (θ y) s
        exact hinv _ ht
      rw [MulAut.inv_apply_self] at h1
      rw [h1]
      exact ht
    have hyW : y ∈ W :=
      Subgroup.mem_inf.2 ⟨(hX y).2 hyst, ⟨⟨hψD, hψfix⟩, hψp⟩⟩
    rw [← map_mul, ← map_mul, hcomm j hj y hyW]
  have hJker : ⁅J, J⁆ ≤ θ.ker := by
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    rw [MonoidHom.mem_ker, commutatorElement_def]
    simp only [map_mul, map_inv]
    have hc := hA (θ a) (θ b) (hJD ha) (hJD hb) (hfix a ha) (hfix b hb)
    calc θ a * θ b * (θ a)⁻¹ * (θ b)⁻¹ = (θ b * θ a) * (θ a)⁻¹ * (θ b)⁻¹ := by rw [hc]
      _ = 1 := by group
  rw [hJperf] at hJker
  have hJp : IsPGroup p J := IsPGroup.to_le hker hJker
  rw [eq_bot_of_perfect_isPGroup hJperf hJp]

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseB
