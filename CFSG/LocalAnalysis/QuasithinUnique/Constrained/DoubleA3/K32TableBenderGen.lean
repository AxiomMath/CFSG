module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableCrit2
public import CFSG.Goldschmidt.Steps.GoldTypeBender

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

section A4Block

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem IsA4Block.le_of_isPGroup {A V W : Subgroup Γ} (hA : IsA4Block A V) (hW : IsPGroup 2 W)
    (hWA : W ≤ A) : W ≤ V := by
  have hWN : W ≤ Subgroup.normalizer (V : Set Γ) := hWA.trans hA.le_normalizer'
  have hmul := C5.card_sup_mul_card_inf_of_le_normalizer hWN
  obtain ⟨k, hk⟩ := hW.exists_card_eq
  have hVW : V ≤ W ⊔ V := le_sup_right
  have hsup : W ⊔ V ≤ A := sup_le hWA hA.le
  have hd12 : Nat.card ↥(W ⊔ V) ∣ 12 := by
    rw [← hA.card_L]
    exact Subgroup.card_dvd_of_le hsup
  have hd4 : 4 ∣ Nat.card ↥(W ⊔ V) := by
    rw [← hA.card_U]
    exact Subgroup.card_dvd_of_le hVW
  have hd2k : Nat.card ↥(W ⊔ V) ∣ 2 ^ (k + 2) := by
    have h1 : Nat.card ↥(W ⊔ V) ∣ Nat.card ↥W * Nat.card ↥V := Dvd.intro _ hmul
    have h2 : Nat.card ↥W * Nat.card ↥V = 2 ^ (k + 2) := by
      rw [hk, hA.card_U]
      ring
    rwa [h2] at h1
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd2k
  have hcard : Nat.card ↥(W ⊔ V) = 4 := by
    rw [hj] at hd12 hd4 ⊢
    have hle : 2 ^ j ≤ 12 := Nat.le_of_dvd (by norm_num) hd12
    have hj3 : j ≤ 3 := by
      by_contra hcon
      have : 2 ^ 4 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases j <;> omega
  have heq : V = W ⊔ V := Subgroup.eq_of_le_of_card_ge hVW (by rw [hcard, hA.card_U])
  exact le_sup_left.trans heq.symm.le

theorem k32_orbit_card_le {A V S R₀ : Subgroup Γ} {c : Γ} (hA : IsA4Block A V) (hS : IsPGroup 2 S)
    (hR₀S : R₀ ≤ S) (hR₀N : R₀ ≤ Subgroup.normalizer (A : Set Γ)) (hcA : c ∈ A)
    (hcS : ∀ s ∈ S, c * s * c⁻¹ ∈ S) :
    Nat.card ↥R₀ ≤ 4 * Nat.card ↥(R₀ ⊓ Subgroup.centralizer ({c} : Set Γ)) := by
  have hmem : ∀ r ∈ R₀, r * c * r⁻¹ ∈ ((fun v => v * c) '' (V : Set Γ)) := by
    intro r hr
    have hrA : r * c * r⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hR₀N hr) c).mp hcA
    have hw : r * c * r⁻¹ * c⁻¹ ∈ A ⊓ S := by
      refine ⟨A.mul_mem hrA (A.inv_mem hcA), ?_⟩
      have h1 : c * r⁻¹ * c⁻¹ ∈ S := hcS _ (S.inv_mem (hR₀S hr))
      have := S.mul_mem (hR₀S hr) h1
      simpa [mul_assoc] using this
    have hwV : r * c * r⁻¹ * c⁻¹ ∈ V :=
      (hA.le_of_isPGroup (hS.to_inf_right (H := A)) inf_le_left) hw
    exact ⟨_, hwV, by group⟩
  have hb := k32_card_le_of_orbit hmem
  have hn : ((fun v => v * c) '' (V : Set Γ)).ncard = 4 := by
    rw [Set.ncard_image_of_injective _ (mul_left_injective c), ← Nat.card_coe_set_eq]
    exact hA.card_U
  rwa [hn] at hb

end A4Block

section Datum

variable {K : Type} [Group K] [Finite K]

theorem k32_datum_bound {X P R A V : Subgroup (MulAut K)} (hd : K32Datum K X P R A V)
    {c : MulAut K} (hcA : c ∈ A) (hcS : ∀ s ∈ P ⊓ innAut K, c * s * c⁻¹ ∈ P ⊓ innAut K) :
    twoPart (innAut K) ≤
      8 * Nat.card ↥((P ⊓ innAut K) ⊓ Subgroup.centralizer ({c} : Set (MulAut K))) := by
  have hJn : (innAut K).Normal := innAut_normal K
  have hXJ : X ≤ Subgroup.normalizer ((innAut K : Subgroup (MulAut K)) : Set (MulAut K)) := by
    rw [Subgroup.normalizer_eq_top (innAut K)]
    exact le_top
  have hPJ : IsSylowTwoOf (P ⊓ innAut K) (innAut K) :=
    A4.isSylowTwoOf_inf_normal hd.sylow hd.inn_le hXJ
  set R₀ := R ⊓ innAut K with hR₀
  have hR₀S : R₀ ≤ P ⊓ innAut K := inf_le_inf_right _ hd.R_le
  have hPJcard : Nat.card ↥(P ⊓ innAut K) ≤ 2 * Nat.card ↥R₀ := by
    have hne : R.relIndex P ≠ 0 := by
      unfold Subgroup.relIndex
      exact Subgroup.index_ne_zero_of_finite
    have h1 : R.relIndex (P ⊓ innAut K) ≤ 2 :=
      le_trans (Subgroup.relIndex_le_of_le_right inf_le_left hne) hd.idx
    have h2 := Subgroup.relIndex_mul_card R (P ⊓ innAut K)
    have h3 : R ⊓ (P ⊓ innAut K) = R₀ := by
      rw [← inf_assoc, inf_eq_left.mpr hd.R_le]
    rw [h3] at h2
    calc Nat.card ↥(P ⊓ innAut K) = R.relIndex (P ⊓ innAut K) * Nat.card ↥R₀ := h2.symm
      _ ≤ 2 * Nat.card ↥R₀ := Nat.mul_le_mul_right _ h1
  have horb := k32_orbit_card_le hd.a4 (hd.sylow.2.1.to_inf_left (K := innAut K)) hR₀S
    (inf_le_left.trans hd.R_norm) hcA hcS
  have hcent : Nat.card ↥(R₀ ⊓ Subgroup.centralizer ({c} : Set (MulAut K))) ≤
      Nat.card ↥((P ⊓ innAut K) ⊓ Subgroup.centralizer ({c} : Set (MulAut K))) :=
    Subgroup.card_le_of_le (inf_le_inf_right _ hR₀S)
  rw [← hPJ.card_eq]
  omega

end Datum

section Phi16

variable {Γ : Type} [Group Γ] [Finite Γ]

omit [Finite Γ] in
theorem k32_comm_mul_central {S Z : Subgroup Γ} (hZS : Z ≤ S)
    (hZc : ∀ z ∈ Z, ∀ s ∈ S, z * s = s * z) {s t z₁ z₂ : Γ} (hs : s ∈ S) (ht : t ∈ S)
    (hz₁ : z₁ ∈ Z) (hz₂ : z₂ ∈ Z) :
    (s * z₁) * (t * z₂) * (s * z₁)⁻¹ * (t * z₂)⁻¹ = s * t * s⁻¹ * t⁻¹ := by
  have h1 : z₁ * t = t * z₁ := hZc z₁ hz₁ t ht
  have h3 : z₁⁻¹ * z₂ = z₂ * z₁⁻¹ := hZc z₁⁻¹ (Z.inv_mem hz₁) z₂ (hZS hz₂)
  have h2 : z₂ * s⁻¹ = s⁻¹ * z₂ := hZc z₂ hz₂ s⁻¹ (S.inv_mem hs)
  calc (s * z₁) * (t * z₂) * (s * z₁)⁻¹ * (t * z₂)⁻¹
      = s * (z₁ * t) * (z₂ * z₁⁻¹) * s⁻¹ * z₂⁻¹ * t⁻¹ := by group
    _ = s * (t * z₁) * (z₁⁻¹ * z₂) * s⁻¹ * z₂⁻¹ * t⁻¹ := by rw [h1, h3]
    _ = s * t * (z₂ * s⁻¹) * z₂⁻¹ * t⁻¹ := by group
    _ = s * t * (s⁻¹ * z₂) * z₂⁻¹ * t⁻¹ := by rw [h2]
    _ = s * t * s⁻¹ * t⁻¹ := by group

theorem k32_card_modEq_three {S : Subgroup Γ} {c : Γ} (hc3 : c ^ 3 = 1)
    (hcS : ∀ s ∈ S, c * s * c⁻¹ ∈ S) :
    Nat.card ↥S ≡ Nat.card ↥(S ⊓ Subgroup.centralizer ({c} : Set Γ)) [MOD 3] := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype ↥S := Fintype.ofFinite _
  let f : Function.End ↥S := fun s => ⟨c * s * c⁻¹, hcS s s.2⟩
  have h3 : c * c * c = 1 := by rw [← pow_three']; exact hc3
  have hf3 : ∀ s : ↥S, f (f (f s)) = s := by
    intro s
    apply Subtype.ext
    show c * (c * (c * (s : Γ) * c⁻¹) * c⁻¹) * c⁻¹ = s
    calc c * (c * (c * (s : Γ) * c⁻¹) * c⁻¹) * c⁻¹ = (c * c * c) * s * (c * c * c)⁻¹ := by group
      _ = s := by rw [h3]; group
  have hf : f ^ 3 ^ 1 = 1 := by
    rw [pow_one]
    funext s
    exact hf3 s
  have h := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 3) (n := 1) hf
  have hfix : Fintype.card (Function.fixedPoints f) =
      Nat.card ↥(S ⊓ Subgroup.centralizer ({c} : Set Γ)) := by
    rw [← Nat.card_eq_fintype_card]
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1 : Γ), x.1.2, ?_⟩
        invFun := fun y => ⟨⟨y.1, y.2.1⟩, ?_⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
    · have hx : c * (x.1 : Γ) * c⁻¹ = x.1 := congrArg Subtype.val x.2
      have hmem : (x.1 : Γ) ∈ Subgroup.centralizer ({c} : Set Γ) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc (x.1 : Γ) * c = c * (x.1 : Γ) * c⁻¹ * c := by rw [hx]
          _ = c * (x.1 : Γ) := by group
      exact hmem
    · apply Subtype.ext
      have hy := Subgroup.mem_centralizer_singleton_iff.mp y.2.2
      show c * (y.1 : Γ) * c⁻¹ = y.1
      calc c * (y.1 : Γ) * c⁻¹ = (y.1 * c) * c⁻¹ := by rw [← hy]
        _ = y.1 := by group
  rw [Nat.card_eq_fintype_card (α := ↥S), ← hfix]
  exact h

theorem k32_phi16 {S Z V : Subgroup Γ} {c : Γ} (hS : IsPGroup 2 S) (hZS : Z ≤ S)
    (hZc : ∀ z ∈ Z, ∀ s ∈ S, z * s = s * z) (hc3 : c ^ 3 = 1)
    (hcS : ∀ s ∈ S, c * s * c⁻¹ ∈ S) (hcZ : ∀ z ∈ Z, c * z * c⁻¹ ∈ Z) (hVZ : V ≤ Z)
    (hV4 : Nat.card ↥V = 4) (hfp : ∀ v ∈ V, v ≠ 1 → c * v * c⁻¹ ≠ v) (hZcomm : Z ≤ ⁅S, S⁆) :
    8 * Nat.card ↥(S ⊓ Subgroup.centralizer ({c} : Set Γ)) < Nat.card ↥S := by
  classical
  set C : Subgroup Γ := S ⊓ Subgroup.centralizer ({c} : Set Γ) with hC
  let H : Subgroup Γ :=
    { carrier := {s | s ∈ S ∧ s⁻¹ * (c * s * c⁻¹) ∈ Z}
      mul_mem' := by
        rintro s t ⟨hs, hsz⟩ ⟨ht, htz⟩
        refine ⟨S.mul_mem hs ht, ?_⟩
        have e : (s * t)⁻¹ * (c * (s * t) * c⁻¹) =
            t⁻¹ * (s⁻¹ * (c * s * c⁻¹)) * t * (t⁻¹ * (c * t * c⁻¹)) := by group
        have hc1 : t⁻¹ * (s⁻¹ * (c * s * c⁻¹)) * t = s⁻¹ * (c * s * c⁻¹) := by
          have h1 := hZc _ hsz t ht
          calc t⁻¹ * (s⁻¹ * (c * s * c⁻¹)) * t
              = t⁻¹ * ((s⁻¹ * (c * s * c⁻¹)) * t) := by group
            _ = t⁻¹ * (t * (s⁻¹ * (c * s * c⁻¹))) := by rw [h1]
            _ = s⁻¹ * (c * s * c⁻¹) := by group
        rw [e, hc1]
        exact Z.mul_mem hsz htz
      one_mem' := ⟨S.one_mem, by simp⟩
      inv_mem' := by
        rintro s ⟨hs, hsz⟩
        refine ⟨S.inv_mem hs, ?_⟩
        have e : s⁻¹⁻¹ * (c * s⁻¹ * c⁻¹) = s * (s⁻¹ * (c * s * c⁻¹))⁻¹ * s⁻¹ := by group
        have h1 := hZc _ (Z.inv_mem hsz) s hs
        have e2 : s * (s⁻¹ * (c * s * c⁻¹))⁻¹ * s⁻¹ = (s⁻¹ * (c * s * c⁻¹))⁻¹ := by
          rw [← h1]; group
        rw [e, e2]
        exact Z.inv_mem hsz }
  have hHS : H ≤ S := fun s hs => hs.1
  have hCH : C ≤ H := by
    intro s hs
    refine ⟨hs.1, ?_⟩
    have hcs : s * c = c * s := Subgroup.mem_centralizer_singleton_iff.mp hs.2
    have : c * s * c⁻¹ = s := by rw [← hcs]; group
    rw [this]
    simp
  have hZH : Z ≤ H := fun z hz => ⟨hZS hz, Z.mul_mem (Z.inv_mem hz) (hcZ z hz)⟩
  have hVC : V ⊓ C = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Subgroup.mem_bot]
    by_contra hv1
    have hvc : v * c = c * v := Subgroup.mem_centralizer_singleton_iff.mp hv.2.2
    exact hfp v hv.1 hv1 (by
      calc c * v * c⁻¹ = v * c * c⁻¹ := by rw [hvc]
        _ = v := by group)
  have hVcent : V ≤ Subgroup.centralizer (C : Set Γ) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact (hZc v (hVZ hv) s hs.1).symm
  have hVN : V ≤ Subgroup.normalizer (C : Set Γ) :=
    hVcent.trans (Subgroup.centralizer_le_normalizer _)
  have hmul := C5.card_sup_mul_card_inf_of_le_normalizer hVN
  rw [hVC, Subgroup.card_bot, hV4] at hmul
  have h4C : 4 * Nat.card ↥C ≤ Nat.card ↥H := by
    have := Subgroup.card_le_of_le (sup_le (hVZ.trans hZH) hCH : V ⊔ C ≤ H)
    omega
  have hHne : ¬ S ≤ H := by
    intro hSH
    have hcomm : ⁅S, S⁆ ≤ Subgroup.centralizer ({c} : Set Γ) := by
      rw [Subgroup.commutator_le]
      intro s hs t ht
      obtain ⟨z₁, hz₁, hs'⟩ : ∃ z ∈ Z, c * s * c⁻¹ = s * z :=
        ⟨s⁻¹ * (c * s * c⁻¹), (hSH hs).2, by group⟩
      obtain ⟨z₂, hz₂, ht'⟩ : ∃ z ∈ Z, c * t * c⁻¹ = t * z :=
        ⟨t⁻¹ * (c * t * c⁻¹), (hSH ht).2, by group⟩
      have key : c * ⁅s, t⁆ * c⁻¹ = ⁅s, t⁆ := by
        have e1 : c * ⁅s, t⁆ * c⁻¹ = ⁅c * s * c⁻¹, c * t * c⁻¹⁆ := by
          simp only [commutatorElement_def]; group
        rw [e1, hs', ht']
        exact k32_comm_mul_central hZS hZc hs ht hz₁ hz₂
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc ⁅s, t⁆ * c = (c * ⁅s, t⁆ * c⁻¹) * c := by rw [key]
        _ = c * ⁅s, t⁆ := by group
    obtain ⟨⟨v, hvV⟩, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
      ((Subgroup.one_lt_card_iff_ne_bot V).mp (by rw [hV4]; norm_num))
    have hv1' : v ≠ 1 := fun h => hv1 (Subtype.ext h)
    have hvc : v * c = c * v :=
      Subgroup.mem_centralizer_singleton_iff.mp (hcomm (hZcomm (hVZ hvV)))
    exact hfp v hvV hv1' (by
      calc c * v * c⁻¹ = v * c * c⁻¹ := by rw [hvc]
        _ = v := by group)
  have hHlt : Nat.card ↥H < Nat.card ↥S := by
    by_contra hcon
    push Not at hcon
    exact hHne (Subgroup.eq_of_le_of_card_ge hHS hcon).ge
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hHS
  have hSpos : 0 < Nat.card ↥S := Nat.card_pos
  have hk2 : 2 ≤ k := by
    rcases k with _ | _ | k
    · simp at hk; omega
    · simp at hk; omega
    · omega
  have hS2 : 2 * Nat.card ↥H ≤ Nat.card ↥S := by rw [hk]; nlinarith
  have h8 : 8 * Nat.card ↥C ≤ Nat.card ↥S := by omega
  have hmod := k32_card_modEq_three hc3 hcS
  refine lt_of_le_of_ne h8 ?_
  intro heq
  have hmod' : Nat.card ↥S % 3 = Nat.card ↥C % 3 := hmod
  have h3C : 3 ∣ Nat.card ↥C := by omega
  obtain ⟨a, ha⟩ := (hS.to_le (inf_le_left : C ≤ S)).exists_card_eq
  rw [ha] at h3C
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3C
  omega

end Phi16

section Quotient

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem k32_V_le_of_inf_ne_bot {A V J : Subgroup Γ} [J.Normal] (hA : IsA4Block A V)
    (hne : V ⊓ J ≠ ⊥) : V ≤ J := by
  have hN₀A : V ⊓ J ≤ A := inf_le_left.trans hA.le
  have hnorm : A ≤ Subgroup.normalizer ((V ⊓ J : Subgroup Γ) : Set Γ) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    have hVa := Subgroup.mem_normalizer_iff.mp (hA.le_normalizer' ha)
    intro y
    constructor
    · rintro ⟨hy1, hy2⟩
      exact ⟨(hVa y).mp hy1, ‹J.Normal›.conj_mem y hy2 a⟩
    · rintro ⟨hy1, hy2⟩
      refine ⟨(hVa y).mpr hy1, ?_⟩
      have := ‹J.Normal›.conj_mem _ hy2 a⁻¹
      simpa [mul_assoc] using this
  exact (k32_le_of_normal_ne_bot hA hN₀A hnorm hne).trans inf_le_right

theorem k32_V_le_of_cyclic_sylow {A V J : Subgroup Γ} [J.Normal] (hA : IsA4Block A V)
    (hcyc : ∀ S : Sylow 2 (Γ ⧸ J), IsCyclic S) : V ≤ J := by
  classical
  by_contra hVJ
  have hbot : V ⊓ J = ⊥ := by
    by_contra hne
    exact hVJ (k32_V_le_of_inf_ne_bot hA hne)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨v₁, hv₁, v₂, hv₂, h1, h2, h12⟩ :=
    CFSG.Goldschmidt.GoldType.exists_ne_one_of_two_lt (S := V) (by rw [hA.card_U]; norm_num)
  have hπ1 : ∀ v ∈ V, QuotientGroup.mk' J v = 1 → v = 1 := by
    intro v hv hπ
    have : v ∈ V ⊓ J := ⟨hv, (QuotientGroup.eq_one_iff v).mp hπ⟩
    rw [hbot] at this
    exact Subgroup.mem_bot.mp this
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [hA.card_U]; norm_num)
  have hVπ : IsPGroup 2 (V.map (QuotientGroup.mk' J)) := hV2.map (QuotientGroup.mk' J)
  obtain ⟨S, hS⟩ := hVπ.exists_le_sylow
  have hcycS : IsCyclic ↥S := hcyc S
  have : Fintype ↥S := Fintype.ofFinite _
  let x : ↥(S : Subgroup (Γ ⧸ J)) := ⟨QuotientGroup.mk' J v₁, hS ⟨v₁, hv₁, rfl⟩⟩
  let y : ↥(S : Subgroup (Γ ⧸ J)) := ⟨QuotientGroup.mk' J v₂, hS ⟨v₂, hv₂, rfl⟩⟩
  have hx2 : x ^ 2 = 1 := Subtype.ext (by
    show (QuotientGroup.mk' J v₁) ^ 2 = 1
    rw [← map_pow, hA.sq_U v₁ hv₁, map_one])
  have hy2 : y ^ 2 = 1 := Subtype.ext (by
    show (QuotientGroup.mk' J v₂) ^ 2 = 1
    rw [← map_pow, hA.sq_U v₂ hv₂, map_one])
  have hx1 : x ≠ 1 := fun h => h1 (hπ1 v₁ hv₁ (congrArg Subtype.val h))
  have hy1 : y ≠ 1 := fun h => h2 (hπ1 v₂ hv₂ (congrArg Subtype.val h))
  have hxy : x ≠ y := by
    intro h
    have hπ : QuotientGroup.mk' J v₁ = QuotientGroup.mk' J v₂ := congrArg Subtype.val h
    apply h12
    have hv : v₁⁻¹ * v₂ = 1 := hπ1 _ (V.mul_mem (V.inv_mem hv₁) hv₂)
      (by rw [map_mul, map_inv, hπ]; group)
    exact (inv_mul_eq_one.mp hv)
  have hle := IsCyclic.card_pow_eq_one_le (α := ↥(S : Subgroup (Γ ⧸ J))) (n := 2) (by norm_num)
  have hsub : ({1, x, y} : Finset ↥(S : Subgroup (Γ ⧸ J))) ⊆
      Finset.univ.filter (fun a : ↥(S : Subgroup (Γ ⧸ J)) => a ^ 2 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl
    · simp
    · exact hx2
    · exact hy2
  have hcard3 : ({1, x, y} : Finset ↥(S : Subgroup (Γ ⧸ J))).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hxy]
    simp [hx1.symm, hy1.symm]
  have := Finset.card_le_card hsub
  omega

theorem k32_A_le_of_comm {A V R D : Subgroup Γ} (hA : IsA4Block A V) (hR2 : IsPGroup 2 R)
    (hRA : R ≤ Subgroup.normalizer (A : Set Γ)) (hRV : R ≤ Subgroup.normalizer (V : Set Γ))
    (hmoves : ¬ R ≤ Subgroup.centralizer (V : Set Γ))
    (hcomm : ∀ x y : Γ, x * y * x⁻¹ * y⁻¹ ∈ D) : A ≤ D := by
  have h := hA.commutator_eq hR2 hRA hRV hmoves
  rw [← h, Subgroup.commutator_le]
  intro a _ r _
  exact hcomm a r

omit [Finite Γ] in
theorem k32_comm_mem_of_isCyclic {J : Subgroup Γ} [J.Normal] (hcyc : IsCyclic (Γ ⧸ J)) (x y : Γ) :
    x * y * x⁻¹ * y⁻¹ ∈ J := by
  rw [← QuotientGroup.eq_one_iff]
  have := hcyc
  have hc : (x : Γ ⧸ J) * (y : Γ ⧸ J) = (y : Γ ⧸ J) * (x : Γ ⧸ J) :=
    (IsCyclic.isMulCommutative (α := Γ ⧸ J)).is_comm.comm _ _
  have := commutatorElement_eq_one_iff_mul_comm.mpr hc
  simpa [commutatorElement_def] using this

omit [Finite Γ] in
theorem k32_le_of_odd_quot {P J : Subgroup Γ} [J.Normal] (hP : IsPGroup 2 P)
    (hodd : Odd (Nat.card (Γ ⧸ J))) : P ≤ J := by
  intro x hx
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  have hxk : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 : orderOf (QuotientGroup.mk' J x) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hxk, map_one])
  have h2 : orderOf (QuotientGroup.mk' J x) ∣ Nat.card (Γ ⧸ J) := orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (Γ ⧸ J)) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
  have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2
  rw [orderOf_eq_one_iff] at this
  exact (QuotientGroup.eq_one_iff x).mp this

end Quotient

end CFSG.QuasithinUnique.DoubleA3
