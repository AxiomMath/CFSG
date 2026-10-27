module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415Sylow
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndLift

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ABGLocalTools HarrisEnd

namespace L415

variable {X : Type} [Group X] [Finite X]

theorem exists_z₁ {β t z : X} (ht : t ∈ centralizer ({β} : Set X)) (ht2 : t * t = 1)
    {Kb₁ Kb₂ : Subgroup (MBar β)}
    (hprod : IsProd (layer (MBar β)) Kb₁ Kb₂ (QuotientGroup.mk ⟨t, ht⟩))
    {W : Subgroup X} (hW : IsSylowOf 2 W (centralizer {β})) (htW : t ∈ W)
    {Dst : Subgroup X} (hDW : Dst ≤ W)
    (hDsyl : IsSylowOf 2 (barOf (centralizer {β}) Dst)
      (layer (MBar β) ⊓ centralizer {QuotientGroup.mk ⟨t, ht⟩}))
    {m : ℕ} (hm : 2 ≤ m) (eD : ↥Dst ≃* DihedralGroup (2 ^ m)) (hzD : z ∈ Dst)
    (hzc : ∀ d ∈ Dst, z * d = d * z) (hz1 : z ≠ 1) :
    ∃ z₁ ∈ W, z₁ ^ 2 = 1 ∧ z = z₁ * (t * z₁ * t⁻¹) ∧ z₁ ≠ t * z₁ * t⁻¹ ∧
      (∀ hz₁ : z₁ ∈ centralizer ({β} : Set X),
        (QuotientGroup.mk ⟨z₁, hz₁⟩ : MBar β) ∈ Kb₁) ∧
      (∀ x ∈ W, ∀ hx : x ∈ centralizer ({β} : Set X), x * z₁ = z₁ * x ↔
        Kb₁.map (MulAut.conj (QuotientGroup.mk ⟨x, hx⟩ : MBar β)).toMonoidHom =
          Kb₁) ∧
      (∀ x ∈ W, x * z₁ ≠ z₁ * x → x * t * z₁ = z₁ * (x * t)) ∧
      ∀ T : Subgroup X, T ≤ W → T ≤ centralizer {t} → Nat.card Dst * Nat.card T ≤ Nat.card W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := centralizer ({β} : Set X) with hMdef
  set tb : MBar β := QuotientGroup.mk ⟨t, ht⟩ with htb
  have hE : (layer (MBar β)).Normal := by
    have := LocalCores.layer_characteristic (G := MBar β)
    infer_instance
  have hWM : W ≤ M := hW.le
  have hWp : IsPGroup 2 W := hW.isPGroup
  have hWb : IsSylowOf 2 (barOf M W) ⊤ := isSylowOf_barOf hW
  have htbW : tb ∈ barOf M W := mk_mem_barOf ht htW
  have htb2 : tb * tb = 1 := by
    rw [htb, ← QuotientGroup.mk_mul]
    have : (⟨t, ht⟩ : ↥M) * ⟨t, ht⟩ = 1 := Subtype.ext ht2
    rw [this, QuotientGroup.mk_one]
  have htbi : tb⁻¹ = tb := inv_eq_of_mul_eq_one_right htb2
  have hDb : barOf M Dst ≤ barOf M W := map_mono fun x hx => hDW hx
  have hDp : IsPGroup 2 Dst := hWp.to_le hDW
  have eDb : ↥(barOf M Dst) ≃* DihedralGroup (2 ^ m) :=
    (barEquiv (hDW.trans hWM) hDp).symm.trans eD
  have hzM : z ∈ M := hWM (hDW hzD)
  set zb : MBar β := QuotientGroup.mk ⟨z, hzM⟩ with hzb
  have hzbD : zb ∈ barOf M Dst := mk_mem_barOf hzM hzD
  have hzbc : ∀ d ∈ barOf M Dst, zb * d = d * zb := by
    rintro _ ⟨d, hd, rfl⟩
    rw [hzb, QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (hzc _ hd)
  have hzb1 : zb ≠ 1 := by
    intro h1
    apply hz1
    have h2 : (QuotientGroup.mk ⟨z, hzM⟩ : MBar β) =
        QuotientGroup.mk ⟨1, one_mem M⟩ := h1
    exact mk_injOn (hDW.trans hWM) hDp hzD (one_mem _) h2
  obtain ⟨zb₁, hzb₁, hzz, hzb₁1, -, hzb₁c, hcen⟩ :=
    hprod.exists_central hE hWb htb2 htbW hDsyl hDb hm eDb hzbD hzbc hzb1
  obtain ⟨z₁', hz₁W, hz₁eq⟩ := mem_barOf.mp hzb₁.1
  set z₁ : X := (z₁' : X) with hz₁def
  have hz₁M : z₁ ∈ M := z₁'.2
  have hmk₁ : (QuotientGroup.mk ⟨z₁, hz₁M⟩ : MBar β) = zb₁ := hz₁eq
  have hinj : ∀ {x y : X} (hx : x ∈ W) (hy : y ∈ W),
      (QuotientGroup.mk ⟨x, hWM hx⟩ : MBar β) = QuotientGroup.mk ⟨y, hWM hy⟩ →
        x = y := fun hx hy h1 => mk_injOn hWM hWp hx hy h1
  have hmk : ∀ {x y : X} (hx : x ∈ M) (hy : y ∈ M),
      (QuotientGroup.mk ⟨x * y, mul_mem hx hy⟩ : MBar β) =
        QuotientGroup.mk ⟨x, hx⟩ * QuotientGroup.mk ⟨y, hy⟩ := fun _ _ => rfl
  have hmki : ∀ {x : X} (hx : x ∈ M),
      (QuotientGroup.mk ⟨x⁻¹, inv_mem hx⟩ : MBar β) =
        (QuotientGroup.mk ⟨x, hx⟩)⁻¹ := fun _ => rfl
  have hcomm : ∀ x ∈ W, ∀ hx : x ∈ M, x * z₁ = z₁ * x ↔
      Kb₁.map (MulAut.conj (QuotientGroup.mk ⟨x, hx⟩ : MBar β)).toMonoidHom =
        Kb₁ := by
    intro x hxW hx
    have hxb : (QuotientGroup.mk ⟨x, hx⟩ : MBar β) ∈ barOf M W :=
      mk_mem_barOf hx hxW
    obtain ⟨hfix, hmove⟩ := hprod.conj_z₁ hzb₁ hzb₁1 hcen hzb₁c hxb
    have hiff : x * z₁ = z₁ * x ↔ (QuotientGroup.mk ⟨x, hx⟩ : MBar β) * zb₁ *
        (QuotientGroup.mk ⟨x, hx⟩)⁻¹ = zb₁ := by
      rw [← hmk₁, ← hmki hx, ← hmk hx hz₁M, ← hmk (mul_mem hx hz₁M) (inv_mem hx)]
      constructor
      · intro h1
        congr 1
        apply Subtype.ext
        show x * z₁ * x⁻¹ = z₁
        rw [h1]
        group
      · intro h1
        have h2 : x * z₁ * x⁻¹ = z₁ := hinj (mul_mem (mul_mem hxW hz₁W) (inv_mem hxW)) hz₁W h1
        calc x * z₁ = x * z₁ * x⁻¹ * x := by group
          _ = z₁ * x := by rw [h2]
    rw [hiff]
    rcases hprod.conj_cases hE (QuotientGroup.mk ⟨x, hx⟩) with h1 | h1
    · exact ⟨fun _ => h1, fun _ => hfix h1⟩
    · exact ⟨fun h2 => absurd h2 (hmove h1), fun h2 => absurd (h2.symm.trans h1)
        hprod.K₁_ne_K₂⟩
  have htK : Kb₁.map (MulAut.conj tb).toMonoidHom = Kb₂ := by
    have := hprod.map_conj
    rwa [htbi] at this
  have ht_not : ¬ (t * z₁ = z₁ * t) := fun h1 =>
    hprod.K₁_ne_K₂ (((hcomm t htW ht).mp h1).symm.trans htK)
  refine ⟨z₁, hz₁W, ?_, ?_, ?_, fun _ => by rw [hmk₁]; exact hzb₁.2, hcomm, ?_, ?_⟩
  ·
    have hsq : (z₁ * z₁) * z₁ = z₁ * (z₁ * z₁) := by group
    have h1 := (hcomm (z₁ * z₁) (mul_mem hz₁W hz₁W) (mul_mem hz₁M hz₁M)).mp hsq
    have hz2 : zb₁ * zb₁ ∈ barOf M W ⊓ Kb₁ := mem_inf.mpr ⟨mul_mem hzb₁.1 hzb₁.1,
      mul_mem hzb₁.2 hzb₁.2⟩
    rcases hcen _ hz2 (fun d hd => by
        rw [mul_assoc, hzb₁c d hd, ← mul_assoc, hzb₁c d hd, mul_assoc]) with h2 | h2
    · rw [sq]
      apply hinj (mul_mem hz₁W hz₁W) (one_mem W)
      rw [hmk hz₁M hz₁M, hmk₁, h2]
      rfl
    · exfalso
      apply hzb₁1
      calc zb₁ = zb₁⁻¹ * (zb₁ * zb₁) := by group
        _ = 1 := by rw [h2, inv_mul_cancel]
  ·
    have htM : t ∈ M := ht
    apply hinj (hDW hzD) (mul_mem hz₁W (mul_mem (mul_mem htW hz₁W) (inv_mem htW)))
    rw [hmk hz₁M (mul_mem (mul_mem htM hz₁M) (inv_mem htM)),
      hmk (mul_mem htM hz₁M) (inv_mem htM), hmk htM hz₁M, hmki htM, hmk₁]
    rw [← htb, ← hzb, hzz, htbi]
  ·
    intro h1
    apply ht_not
    calc t * z₁ = t * (t * z₁ * t⁻¹) := by rw [← h1]
      _ = (t * t) * z₁ * t⁻¹ := by group
      _ = z₁ * t := by rw [ht2, one_mul, inv_eq_of_mul_eq_one_right ht2]
  ·
    intro x hxW hxz
    have hx : x ∈ M := hWM hxW
    have h1 : Kb₁.map (MulAut.conj (QuotientGroup.mk ⟨x, hx⟩ :
        MBar β)).toMonoidHom = Kb₂ := by
      rcases hprod.conj_cases hE (QuotientGroup.mk ⟨x, hx⟩) with h2 | h2
      · exact absurd ((hcomm x hxW hx).mpr h2) hxz
      · exact h2
    refine (hcomm (x * t) (mul_mem hxW htW) (mul_mem hx ht)).mpr ?_
    rcases hprod.conj_cases hE (QuotientGroup.mk ⟨x * t, mul_mem hx ht⟩) with h2 | h2
    · exact h2
    · exfalso
      have hcomp : (MulAut.conj (QuotientGroup.mk ⟨x * t, mul_mem hx ht⟩ :
          MBar β)).toMonoidHom = (MulAut.conj (QuotientGroup.mk ⟨x, hx⟩ :
            MBar β)).toMonoidHom.comp (MulAut.conj tb).toMonoidHom := by
        ext y
        simp [MulAut.conj_apply, hmk hx ht, htb, mul_assoc]
      have h3 : Kb₂.map (MulAut.conj (QuotientGroup.mk ⟨x, hx⟩ :
          MBar β)).toMonoidHom = Kb₂ := by
        rw [← htK, map_map, ← hcomp, h2, htK]
      apply hprod.K₁_ne_K₂
      exact map_injective (MulAut.conj (QuotientGroup.mk ⟨x, hx⟩ :
        MBar β)).injective (h1.trans h3.symm)
  ·
    intro T hTW hTt
    have hTp : IsPGroup 2 T := hWp.to_le hTW
    have hTb : barOf M T ≤ barOf M W := map_mono fun x hx => hTW hx
    have hTbt : barOf M T ≤ centralizer {tb} := by
      rintro _ ⟨y, hy, rfl⟩
      rw [mem_centralizer_singleton_iff]
      have hyt : (y : X) * t = t * y := mem_centralizer_singleton_iff.mp (hTt hy)
      show (QuotientGroup.mk (y * ⟨t, ht⟩) : MBar β) =
        QuotientGroup.mk (⟨t, ht⟩ * y)
      congr 1
      exact Subtype.ext hyt
    have h1 := hprod.card_mul_le hE hWb htb2 hTb hTbt
    rw [card_barOf (hTW.trans hWM) hTp, card_barOf hWM hWp] at h1
    have h2 : Nat.card ↥(barOf M W ⊓ Kb₁) = Nat.card Dst := by
      rw [(hprod.isSylowOf_inf_K₁ hE hWb).card_eq, ← card_barOf (hDW.trans hWM) hDp,
        hDsyl.card_eq, hprod.card_centralizer htb2]
    rwa [h2] at h1

end L415

end CFSG.ComponentClassification.HarrisLit
