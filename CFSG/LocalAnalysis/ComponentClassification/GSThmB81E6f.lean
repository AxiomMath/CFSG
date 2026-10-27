module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81E6c
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81E6n

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace Hyp59

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H}

namespace L81Hyp

variable {H₁ : h.L81Hyp}

namespace Data

variable {d : Data H₁}

section Field

variable {v : H} (hv : d.IsV v) (I : In81) (F : d.Facts) (hJo : CFSec8JOrder) (hL0 : CF81L0)
  (hCls : CF81E6Cls) (hOut : CF81E6Out) (hFld : CF81E6Fld)
include hv I F hJo hL0 hCls hOut hFld

theorem false_of_field (T : Sylow 2 H) (hTW : (T : Subgroup H) ≤ h.W) (hBT : h.B ≤ T)
    (haT : h.a ∈ (T : Subgroup H)) (R : Sylow 2 ↥h.M3)
    (hR : (R : Subgroup ↥h.M3) = (T : Subgroup H).subgroupOf h.M3) {ψ : H} (hψT : ψ ∈ T)
    (hψN : H₁.psiW ⟨ψ, hTW hψT⟩ ∉ Cat8.innA (h.K ⧸ pPrimeCore 2 h.K) H₁.kloc.rhoA)
    (hψ2 : ψ * ψ ∈ (T : Subgroup H) ⊓ h.M3) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker := H₁.kloc.not_two_dvd_card_ker_modelHom I.cf1 I.cf2
  obtain ⟨-, p, f, hp, hp2, hf, hK, hJ⟩ := Hyp52.Sec8Case.exists_params h.toHyp52 H₁.kloc.case8
  have hadm := H₁.kloc.rhoA_admQ I.cf1 I.cf2 hJo hp hp2 hf hJ
  set N := Cat8.innA (h.K ⧸ pPrimeCore 2 h.K) H₁.kloc.rhoA with hN
  set S₀ := (R : Subgroup ↥h.M3).map H₁.kloc.rho with hS₀
  have hS₀N : S₀ ≤ N := by
    have h1 : S₀ ≤ H₁.kloc.rho.range := map_le_range _ _
    rwa [H₁.kloc.rho_range_eq] at h1
  have hsyl : ∃ P : Sylow 2 ↥N, (P : Subgroup _) = S₀.subgroupOf N := by
    have h1 := E6.exists_sylow_map H₁.kloc.rho R
    rwa [H₁.kloc.rho_range_eq] at h1
  have hRmem : ∀ x : ↥h.M3, x ∈ (R : Subgroup ↥h.M3) ↔ (x : H) ∈ (T : Subgroup H) := by
    intro x
    rw [hR]
    rfl
  have hQ0 : ∀ {t : H}, t ∈ (T : Subgroup H) → ∀ {q : H}, q ∈ (T : Subgroup H) ⊓ h.M3 →
      t * q * t⁻¹ ∈ (T : Subgroup H) ⊓ h.M3 := fun {_} ht {_} hq =>
    Q0_normal hv I F hJo hL0 hCls hOut T hTW hBT haT R hR ht hq
  have hconjS : ∀ (y : H) (hyT : y ∈ (T : Subgroup H)), ∀ s ∈ S₀,
      H₁.psiW ⟨y, hTW hyT⟩ * s * (H₁.psiW ⟨y, hTW hyT⟩)⁻¹ ∈ S₀ := by
    intro y hyT s hs
    obtain ⟨r, hr, rfl⟩ := mem_map.mp hs
    obtain ⟨h1T, h1M⟩ := mem_inf.mp (hQ0 hyT (mem_inf.mpr ⟨(hRmem r).mp hr, r.2⟩))
    refine mem_map.mpr ⟨⟨y * r * y⁻¹, h1M⟩, (hRmem _).mpr h1T, ?_⟩
    have e : (⟨y * (r : H) * y⁻¹, h.toHyp52.M3_le_normalizer h1M⟩ : ↥h.W) =
        ⟨y, hTW hyT⟩ * ⟨r, h.toHyp52.M3_le_normalizer r.2⟩ * ⟨y, hTW hyT⟩⁻¹ := rfl
    rw [← psiW_eq_rho (H₁ := H₁) h1M, e, map_mul, map_mul, map_inv, psiW_eq_rho (H₁ := H₁) r.2]
  set ψW : ↥h.W := ⟨ψ, hTW hψT⟩ with hψW
  have hψnorm : H₁.psiW ψW ∈ normalizer (S₀ : Set (MulAut (h.K ⧸ pPrimeCore 2 h.K))) := by
    rw [mem_normalizer_iff]
    intro s
    refine ⟨hconjS ψ hψT s, fun hs => ?_⟩
    have h1 := hconjS ψ⁻¹ (inv_mem hψT) _ hs
    have e : (⟨ψ⁻¹, hTW (inv_mem hψT)⟩ : ↥h.W) = ψW⁻¹ := rfl
    rwa [e, map_inv, inv_inv, show (H₁.psiW ψW)⁻¹ * (H₁.psiW ψW * s * (H₁.psiW ψW)⁻¹) *
      H₁.psiW ψW = s by group] at h1
  have hψ2S : H₁.psiW ψW * H₁.psiW ψW ∈ S₀ := by
    obtain ⟨h2T, h2M⟩ := mem_inf.mp hψ2
    refine mem_map.mpr ⟨⟨ψ * ψ, h2M⟩, (hRmem _).mpr h2T, ?_⟩
    rw [← psiW_eq_rho (H₁ := H₁) h2M, ← map_mul]
    rfl
  obtain ⟨σ, hσS, hσ2, E, hES, hEC, hE2, hE16⟩ :=
    hFld _ p f hp hp2 hf hK _ hadm S₀ hsyl hS₀N (H₁.psiW ψW) hψnorm hψN hψ2S
  obtain ⟨r₀, hr₀, rfl⟩ := mem_map.mp hσS
  have hr₀T : (r₀ : H) ∈ (T : Subgroup H) := (hRmem r₀).mp hr₀
  set η : H := (r₀ : H) * ψ with hη
  have hηT : η ∈ (T : Subgroup H) := mul_mem hr₀T hψT
  have hψη : H₁.psiW ⟨η, hTW hηT⟩ = H₁.kloc.rho r₀ * H₁.psiW ψW := by
    have e : (⟨η, hTW hηT⟩ : ↥h.W) = ⟨r₀, h.toHyp52.M3_le_normalizer r₀.2⟩ * ψW := rfl
    rw [e, map_mul, psiW_eq_rho (H₁ := H₁) r₀.2]
  have hbM : d.b ∉ h.M3 := fun hb => d.e6_not_conj_b_M3 hv I hJo hL0 hCls F 1 (by
    rw [show (1 : H)⁻¹ * d.b * 1 = d.b by group]
    exact hb)
  have hη2 : η * η = 1 := by
    have hη2T : η * η ∈ (T : Subgroup H) := mul_mem hηT hηT
    have hB : η * η ∈ h.B := by
      refine mem_B_of_psiW (H₁ := H₁) T.isPGroup' hTW hBT hη2T ?_
      have e : (⟨η * η, hTW hη2T⟩ : ↥h.W) = ⟨η, hTW hηT⟩ * ⟨η, hTW hηT⟩ := rfl
      rw [e, map_mul, hψη]
      exact hσ2
    have hM : η * η ∈ h.M3 := by
      have h1 := (mem_inf.mp (hQ0 hψT (mem_inf.mpr ⟨hr₀T, r₀.2⟩))).2
      rw [show η * η = (r₀ : H) * (ψ * r₀ * ψ⁻¹) * (ψ * ψ) by rw [hη]; group]
      exact mul_mem (mul_mem r₀.2 h1) (mem_inf.mp hψ2).2
    rcases mem_zpowers_two d.b_ord (d.B_eq ▸ hB) with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hM) hbM
  set E'' : Subgroup ↥h.M3 := E.comap H₁.kloc.rho ⊓ (R : Subgroup ↥h.M3) with hE''
  have hE''2 : IsPGroup 2 E'' := R.isPGroup'.to_le inf_le_right
  have hE''map : E''.map H₁.kloc.rho = E := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (mem_inf.mp hx).1
    · intro e he
      obtain ⟨x, hx, rfl⟩ := mem_map.mp (hES he)
      exact mem_map_of_mem _ (mem_inf.mpr ⟨he, hx⟩)
  have hE''card : Nat.card E'' = 16 := by
    rw [← Eight.card_map_of_isPGroup hker hE''2, hE''map, hE16]
  set E' : Subgroup H := E''.map h.M3.subtype with hE'
  have hE'card : Nat.card E' = 16 := by
    rw [hE', card_map_of_injective h.M3.subtype_injective, hE''card]
  have hE'M : E' ≤ h.M3 := map_subtype_le _
  have hE'2 : ∀ e ∈ E', e * e = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hxE, hxR⟩ := mem_inf.mp hx
    have h1 := Eight.injOn_of_isPGroup hker R.isPGroup' (mul_mem hxR hxR) (one_mem _)
      (by rw [map_mul, map_one]; exact hE2 _ hxE)
    exact congrArg Subtype.val h1
  have hηE : ∀ e ∈ E', e * η = η * e := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hxE, hxR⟩ := mem_inf.mp hx
    obtain ⟨h1T, h1M⟩ := mem_inf.mp (hQ0 hηT (mem_inf.mpr ⟨(hRmem x).mp hxR, x.2⟩))
    have hρ : H₁.kloc.rho ⟨η * x * η⁻¹, h1M⟩ = H₁.kloc.rho x := by
      have e : (⟨η * (x : H) * η⁻¹, h.toHyp52.M3_le_normalizer h1M⟩ : ↥h.W) =
          ⟨η, hTW hηT⟩ * ⟨x, h.toHyp52.M3_le_normalizer x.2⟩ * ⟨η, hTW hηT⟩⁻¹ := rfl
      rw [← psiW_eq_rho (H₁ := H₁) h1M, e, map_mul, map_mul, map_inv,
        psiW_eq_rho (H₁ := H₁) x.2, hψη]
      have hc := mem_centralizer_iff.mp (hEC hxE) _ (Set.mem_singleton _)
      rw [hc, mul_inv_cancel_right]
    have h2 := Eight.injOn_of_isPGroup hker R.isPGroup' ((hRmem _).mpr h1T) hxR hρ
    have h3 : η * (x : H) * η⁻¹ = x := congrArg Subtype.val h2
    calc (x : H) * η = η * x * η⁻¹ * η := by rw [h3]
      _ = η * x := by group
  have hbη : d.b * η = η * d.b := (d.comm_b_of_mem_W (hTW hηT)).symm
  have hbE : ∀ e ∈ E', e * d.b = d.b * e := fun e he =>
    d.comm_b_of_mem_W (h.toHyp52.M3_le_normalizer (hE'M he))
  set Z : Subgroup H := (N.comap H₁.psiW).map h.W.subtype with hZ
  have hMZ : h.M3 ≤ Z := fun m hm => ⟨⟨m, h.toHyp52.M3_le_normalizer hm⟩, psiW_mem_innA hm, rfl⟩
  have hBZ : h.B ≤ Z := fun y hy => ⟨⟨y, le_normalizer hy⟩, by
    show H₁.psiW ⟨y, le_normalizer hy⟩ ∈ N
    rw [psiW_B hy]
    exact one_mem _, rfl⟩
  have hbB : d.b ∈ h.B := d.B_eq ▸ mem_zpowers d.b
  have hE'b : E' ⊔ zpowers d.b ≤ Z := sup_le (hE'M.trans hMZ) ((zpowers_le.mpr hbB).trans hBZ)
  have hηZ : η ∉ E' ⊔ zpowers d.b := by
    intro hη'
    obtain ⟨y, hy, hyη⟩ := hE'b hη'
    have hy' : y = ⟨η, hTW hηT⟩ := Subtype.ext hyη
    rw [hy'] at hy
    apply hψN
    have h1 : H₁.psiW ψW = (H₁.kloc.rho r₀)⁻¹ * H₁.psiW ⟨η, hTW hηT⟩ := by
      rw [hψη, inv_mul_cancel_left]
    rw [h1]
    exact mul_mem (inv_mem (hS₀N hσS)) hy
  have hb2 : d.b * d.b = 1 := d.b_mul_self
  have hcard32 : Nat.card ↥(E' ⊔ zpowers d.b) = 32 := by
    rw [E6.card_sup_zpowers hb2 (fun h1 => hbM (hE'M h1)) hbE, hE'card]
  have hE₃₂2 := E6.mul_self_of_mem_sup_zpowers hE'2 hb2 hbE
  have hηE₃₂ := E6.comm_of_mem_sup_zpowers hηE hbη
  have hcard64 : Nat.card ↥((E' ⊔ zpowers d.b) ⊔ zpowers η) = 64 := by
    rw [E6.card_sup_zpowers hη2 hηZ hηE₃₂, hcard32]
  have h64 := card_elem_le_H hv I F (E6.mul_self_of_mem_sup_zpowers hE₃₂2 hη2 hηE₃₂)
  omega

theorem T_mod_Q0_cyclic (T : Sylow 2 H) (hTW : (T : Subgroup H) ≤ h.W) (hBT : h.B ≤ T)
    (haT : h.a ∈ (T : Subgroup H)) (R : Sylow 2 ↥h.M3)
    (hR : (R : Subgroup ↥h.M3) = (T : Subgroup H).subgroupOf h.M3) :
    ∃ c ∈ (T : Subgroup H), ∀ t ∈ (T : Subgroup H), ∃ k : ℤ,
      (c ^ k)⁻¹ * t ∈ (T : Subgroup H) ⊓ h.M3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := Cat8.innA (h.K ⧸ pPrimeCore 2 h.K) H₁.kloc.rhoA with hN
  set Q₀ := (T : Subgroup H) ⊓ h.M3 with hQ₀
  have hb2 : d.b * d.b = 1 := d.b_mul_self
  have hbT : d.b ∈ (T : Subgroup H) := hBT (d.B_eq ▸ mem_zpowers d.b)
  have hT1 : ∀ (t : H) (ht : t ∈ (T : Subgroup H)), H₁.psiW ⟨t, hTW ht⟩ ∈ N →
      t ∈ Q₀ ∨ t * d.b ∈ Q₀ := by
    intro t ht hψ
    obtain ⟨r, hr, hrb⟩ := exists_mem_T_M3 T hTW hBT R hR ht hψ
    rcases mem_zpowers_two d.b_ord (d.B_eq ▸ hrb) with h1 | h1
    · left
      rw [← inv_mul_eq_one.mp h1]
      exact hr
    · right
      have ht' : t = r * d.b := by rw [← h1, mul_inv_cancel_left]
      rw [ht', mul_assoc, hb2, mul_one]
      exact hr
  obtain ⟨t₀, ht₀T, ht₀⟩ := exists_gen_mod_innA I.cf1 I.cf2 hJo hOut (T : Subgroup H) hTW
  have hpow : ∀ n : ℕ, ((t₀ ^ n : ↥h.W) : H) = (t₀ : H) ^ n := fun n => SubgroupClass.coe_pow _ _
  obtain ⟨r, hr⟩ := IsPGroup.iff_orderOf.mp T.isPGroup' ⟨t₀, ht₀T⟩
  have hex : ∃ j : ℕ, H₁.psiW t₀ ^ 2 ^ j ∈ N := by
    refine ⟨r, ?_⟩
    have h1 : t₀ ^ 2 ^ r = 1 := by
      apply Subtype.ext
      have h2 := congrArg Subtype.val (pow_orderOf_eq_one (⟨t₀, ht₀T⟩ : ↥(T : Subgroup H)))
      rw [hr] at h2
      rw [hpow]
      simpa using h2
    rw [← map_pow, h1, map_one]
    exact one_mem _
  classical
  by_cases hm0 : Nat.find hex = 0
  ·
    have ht₀N : H₁.psiW t₀ ∈ N := by
      have h1 := Nat.find_spec hex
      rwa [hm0, pow_zero, pow_one] at h1
    refine ⟨d.b, hbT, fun t ht => ?_⟩
    obtain ⟨k, hk⟩ := ht₀ t ht
    have hψt : H₁.psiW ⟨t, hTW ht⟩ ∈ N := by
      have h1 := mul_mem (zpow_mem ht₀N k) hk
      rwa [mul_inv_cancel_left] at h1
    rcases hT1 t ht hψt with h1 | h1
    · exact ⟨0, by rwa [zpow_zero, inv_one, one_mul]⟩
    · refine ⟨1, ?_⟩
      rw [zpow_one, inv_eq_of_mul_eq_one_right hb2, ← d.comm_b_of_mem_W (hTW ht)]
      exact h1
  · obtain ⟨m', hm'⟩ := Nat.exists_eq_succ_of_ne_zero hm0
    have hψT : (t₀ : H) ^ 2 ^ m' ∈ (T : Subgroup H) := pow_mem ht₀T _
    have hψN : H₁.psiW ⟨(t₀ : H) ^ 2 ^ m', hTW hψT⟩ ∉ N := by
      have e : (⟨(t₀ : H) ^ 2 ^ m', hTW hψT⟩ : ↥h.W) = t₀ ^ 2 ^ m' :=
        Subtype.ext (hpow _).symm
      rw [e, map_pow]
      exact Nat.find_min hex (by omega)
    have hψ2T : (t₀ : H) ^ 2 ^ m' * (t₀ : H) ^ 2 ^ m' ∈ (T : Subgroup H) := mul_mem hψT hψT
    have hψ2N : H₁.psiW ⟨(t₀ : H) ^ 2 ^ m' * (t₀ : H) ^ 2 ^ m', hTW hψ2T⟩ ∈ N := by
      have e : (⟨(t₀ : H) ^ 2 ^ m' * (t₀ : H) ^ 2 ^ m', hTW hψ2T⟩ : ↥h.W) =
          t₀ ^ 2 ^ Nat.find hex := by
        apply Subtype.ext
        rw [hpow, hm', pow_succ, pow_mul, sq]
      rw [e, map_pow]
      exact Nat.find_spec hex
    have hψ2Q : (t₀ : H) ^ 2 ^ m' * (t₀ : H) ^ 2 ^ m' ∉ Q₀ := fun hQ =>
      false_of_field hv I F hJo hL0 hCls hOut hFld T hTW hBT haT R hR hψT hψN hQ
    have hψ2b := (hT1 _ hψ2T hψ2N).resolve_left hψ2Q
    refine ⟨t₀, ht₀T, fun t ht => ?_⟩
    obtain ⟨k, hk⟩ := ht₀ t ht
    have hyT : ((t₀ : H) ^ k)⁻¹ * t ∈ (T : Subgroup H) :=
      mul_mem (inv_mem (zpow_mem ht₀T k)) ht
    have hyN : H₁.psiW ⟨((t₀ : H) ^ k)⁻¹ * t, hTW hyT⟩ ∈ N := by
      have e : (⟨((t₀ : H) ^ k)⁻¹ * t, hTW hyT⟩ : ↥h.W) = (t₀ ^ k)⁻¹ * ⟨t, hTW ht⟩ :=
        Subtype.ext (by rw [MulMemClass.coe_mul, InvMemClass.coe_inv, SubgroupClass.coe_zpow])
      rw [e, map_mul, map_inv, map_zpow]
      exact hk
    rcases hT1 _ hyT hyN with h1 | h1
    · exact ⟨k, h1⟩
    · refine ⟨k + ((2 ^ Nat.find hex : ℕ) : ℤ), ?_⟩
      set ψ := (t₀ : H) ^ 2 ^ m' with hψ
      have hψψ : (t₀ : H) ^ (((2 ^ Nat.find hex : ℕ) : ℤ)) = ψ * ψ := by
        rw [zpow_natCast, hm', pow_succ, pow_mul, sq]
      have hb' : d.b⁻¹ * ((ψ * ψ)⁻¹ * (((t₀ : H) ^ k)⁻¹ * t)) * d.b =
          (ψ * ψ)⁻¹ * (((t₀ : H) ^ k)⁻¹ * t) := by
        rw [mul_assoc, d.comm_b_of_mem_W (hTW (mul_mem (inv_mem hψ2T) hyT)),
          inv_mul_cancel_left]
      have e : ((t₀ : H) ^ (k + ((2 ^ Nat.find hex : ℕ) : ℤ)))⁻¹ * t =
          (ψ * ψ * d.b)⁻¹ * (((t₀ : H) ^ k)⁻¹ * t * d.b) := by
        rw [zpow_add, hψψ]
        calc ((t₀ : H) ^ k * (ψ * ψ))⁻¹ * t = (ψ * ψ)⁻¹ * (((t₀ : H) ^ k)⁻¹ * t) := by group
          _ = d.b⁻¹ * ((ψ * ψ)⁻¹ * (((t₀ : H) ^ k)⁻¹ * t)) * d.b := hb'.symm
          _ = (ψ * ψ * d.b)⁻¹ * (((t₀ : H) ^ k)⁻¹ * t * d.b) := by group
      rw [e]
      exact mul_mem (inv_mem hψ2b) h1

end Field

end Data

end L81Hyp

end Hyp59

end CFSG.ComponentClassification.GSThmB
