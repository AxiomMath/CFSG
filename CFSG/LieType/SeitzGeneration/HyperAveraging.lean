module

public import CFSG.LieType.SeitzGeneration.NonabAveraging
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Data.ZMod.QuotientGroup

public section

namespace CFSG.LieType.SeitzGeneration

section Hyper

variable {F M E : Type*} [Field F] [AddCommGroup M] [Module F M] [Group E]

@[expose] def hyperFixed (ρ : E →* Module.End F M) (N : Subgroup E) : Submodule F M :=
  ⨅ n ∈ N, LinearMap.ker (ρ n - 1)

theorem mem_hyperFixed {ρ : E →* Module.End F M} {N : Subgroup E} {m : M} :
    m ∈ hyperFixed ρ N ↔ ∀ n ∈ N, ρ n m = m := by
  simp [hyperFixed, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

theorem mem_hyperFixed_sup_zpowers {ρ : E →* Module.End F M} {N : Subgroup E} {x : E} {m : M}
    (hN : m ∈ hyperFixed ρ N) (hx : ρ x m = m) :
    m ∈ hyperFixed ρ (N ⊔ Subgroup.zpowers x) := by
  let T : Subgroup E :=
    { carrier := {e | ρ e m = m}
      mul_mem' := fun {a b} ha hb => by
        change ρ (a * b) m = m
        rw [map_mul, Module.End.mul_apply]
        change ρ a m = m at ha
        change ρ b m = m at hb
        rw [hb, ha]
      one_mem' := by
        change ρ 1 m = m
        simp
      inv_mem' := fun {a} ha => by
        change ρ a⁻¹ m = m
        change ρ a m = m at ha
        calc ρ a⁻¹ m = ρ a⁻¹ (ρ a m) := by rw [ha]
          _ = m := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl }
  have hle : N ⊔ Subgroup.zpowers x ≤ T :=
    sup_le (fun n hn => (mem_hyperFixed.1 hN) n hn) (Subgroup.zpowers_le.2 hx)
  exact mem_hyperFixed.2 fun e he => hle he

theorem apply_mem_hyperFixed {ρ : E →* Module.End F M} (hcomm : ∀ a b : E, a * b = b * a)
    {N : Subgroup E} (e : E) {m : M} (hm : m ∈ hyperFixed ρ N) : ρ e m ∈ hyperFixed ρ N := by
  rw [mem_hyperFixed] at hm ⊢
  intro n hn
  rw [← Module.End.mul_apply, ← map_mul, hcomm, map_mul, Module.End.mul_apply, hm n hn]

end Hyper

section Index

variable {E : Type*} [Group E] [Finite E]

theorem hyper_index_sup_zpowers {p : ℕ} [Fact p.Prime] (hcomm : ∀ a b : E, a * b = b * a)
    (N : Subgroup E) {x : E} (hx : x ∉ N) (hxp : x ^ p = 1) :
    (N ⊔ Subgroup.zpowers x).index * p = N.index := by
  have hpr : p.Prime := Fact.out
  have hnorm : N.Normal := ⟨fun n hn g => by rw [hcomm g n, mul_inv_cancel_right]; exact hn⟩
  have hx1 : x ≠ 1 := fun h => hx (h ▸ N.one_mem)
  have hord : orderOf x = p := orderOf_eq_prime hxp hx1
  have hinf : Nat.card (N ⊓ Subgroup.zpowers x : Subgroup E) = 1 := by
    have hdvd : Nat.card (N ⊓ Subgroup.zpowers x : Subgroup E) ∣ p := by
      have := Subgroup.card_dvd_of_le (inf_le_right : N ⊓ Subgroup.zpowers x ≤ _)
      rwa [Nat.card_zpowers, hord] at this
    rcases (Nat.dvd_prime hpr).1 hdvd with h | h
    · exact h
    · exfalso
      apply hx
      have hle : N ⊓ Subgroup.zpowers x ≤ Subgroup.zpowers x := inf_le_right
      have hcard : Nat.card (Subgroup.zpowers x) =
          Nat.card (N ⊓ Subgroup.zpowers x : Subgroup E) := by
        rw [Nat.card_zpowers, hord, h]
      have heq := Subgroup.eq_of_le_of_card_ge hle hcard.le
      have hxmem : x ∈ N ⊓ Subgroup.zpowers x := by
        rw [heq]
        exact Subgroup.mem_zpowers x
      exact hxmem.1
  have h1 : N.relIndex (Subgroup.zpowers x) = p := by
    have := Subgroup.relIndex_mul_card N (Subgroup.zpowers x)
    rwa [hinf, mul_one, Nat.card_zpowers, hord] at this
  have h2 := Subgroup.relIndex_mul_index (le_sup_left : N ≤ N ⊔ Subgroup.zpowers x)
  rw [Subgroup.relIndex_sup_left, h1] at h2
  rw [mul_comm]
  exact h2

end Index

section Averaging

variable {F M E : Type*} [Field F] [AddCommGroup M] [Module F M] [Group E]

theorem mem_iSup_hyperFixed [Finite E] {p : ℕ} [Fact p.Prime] (hpF : (p : F) ≠ 0)
    (hcomm : ∀ a b : E, a * b = b * a) (hexp : ∀ a : E, a ^ p = 1) (ρ : E →* Module.End F M)
    (S : Submodule F M) (hS : ∀ (e : E), ∀ x ∈ S, ρ e x ∈ S) :
    ∀ (k : ℕ) (N : Subgroup E), 1 ≤ k → N.index = p ^ k → ∀ m ∈ S, m ∈ hyperFixed ρ N →
      m ∈ ⨆ (F' : Subgroup E) (_ : N ≤ F' ∧ F'.index = p), hyperFixed ρ F' ⊓ S := by
  have hpr : p.Prime := Fact.out
  have hp2 : 2 ≤ p := hpr.two_le
  intro k
  induction k with
  | zero => intro N h; omega
  | succ k ih =>
    intro N _ hN m hmS hmN
    rcases Nat.eq_zero_or_pos k with rfl | hk
    ·
      refine Submodule.mem_iSup_of_mem N (Submodule.mem_iSup_of_mem ⟨le_rfl, ?_⟩ ?_)
      · simpa using hN
      · exact ⟨hmN, hmS⟩
    ·
      set T : Submodule F M := ⨆ (F' : Subgroup E) (_ : N ≤ F' ∧ F'.index = p),
        hyperFixed ρ F' ⊓ S with hT
      have hNtop : N ≠ ⊤ := by
        intro h
        rw [h, Subgroup.index_top] at hN
        have : 2 ≤ p ^ (k + 1) := hp2.trans (by
          calc p = p ^ 1 := (pow_one p).symm
            _ ≤ p ^ (k + 1) := Nat.pow_le_pow_right hpr.pos (by omega))
        omega
      obtain ⟨z, hz⟩ : ∃ z : E, z ∉ N := by
        by_contra h
        push Not at h
        exact hNtop (Subgroup.eq_top_iff' N |>.2 h)
      have hN₂ : (N ⊔ Subgroup.zpowers z).index = p ^ k := by
        have h1 := hyper_index_sup_zpowers (p := p) hcomm N hz (hexp z)
        rw [hN, pow_succ] at h1
        exact Nat.eq_of_mul_eq_mul_right hpr.pos h1
      obtain ⟨y, hy⟩ : ∃ y : E, y ∉ N ⊔ Subgroup.zpowers z := by
        by_contra h
        push Not at h
        have htop : N ⊔ Subgroup.zpowers z = ⊤ := (Subgroup.eq_top_iff' _).2 h
        rw [htop, Subgroup.index_top] at hN₂
        have : 2 ≤ p ^ k := hp2.trans (by
          calc p = p ^ 1 := (pow_one p).symm
            _ ≤ p ^ k := Nat.pow_le_pow_right hpr.pos hk)
        omega
      have hAB : Commute (ρ y) (ρ z) := (show Commute y z from hcomm y z).map ρ
      have hA : ρ y ^ p = 1 := by rw [← map_pow, hexp, map_one]
      have hB : ρ z ^ p = 1 := by rw [← map_pow, hexp, map_one]
      obtain ⟨u, v, hu, hv, hsum, hmem⟩ := exists_decomp_lines hpF hAB hA hB m
      set S' : Submodule F M := hyperFixed ρ N ⊓ S with hS'
      have hAS : ∀ x ∈ S', ρ y x ∈ S' := fun x hx =>
        ⟨apply_mem_hyperFixed hcomm y hx.1, hS y x hx.2⟩
      have hBS : ∀ x ∈ S', ρ z x ∈ S' := fun x hx =>
        ⟨apply_mem_hyperFixed hcomm z hx.1, hS z x hx.2⟩
      obtain ⟨huS, hvS⟩ := hmem S' hAS hBS ⟨hmN, hmS⟩
      have hu_mem : ∀ j : ZMod p, u j ∈ T := fun j => by
        have hfix : ρ (y * z ^ j.val) (u j) = u j := by
          have := hu j
          rwa [← map_pow, ← map_mul] at this
        have hxj : y * z ^ j.val ∉ N := fun h => hy (by
          have hzj : z ^ j.val ∈ N ⊔ Subgroup.zpowers z :=
            Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers z) _)
          have h3 : y * z ^ j.val * (z ^ j.val)⁻¹ ∈ N ⊔ Subgroup.zpowers z :=
            Subgroup.mul_mem _ (Subgroup.mem_sup_left h) ((N ⊔ Subgroup.zpowers z).inv_mem hzj)
          simpa using h3)
        have hN₁ : (N ⊔ Subgroup.zpowers (y * z ^ j.val)).index = p ^ k := by
          have hc : Commute y (z ^ j.val) := hcomm y _
          have h1 := hyper_index_sup_zpowers (p := p) hcomm N hxj (by
            rw [hc.mul_pow, hexp y, one_mul, ← pow_mul, mul_comm, pow_mul, hexp z, one_pow])
          rw [hN, pow_succ] at h1
          exact Nat.eq_of_mul_eq_mul_right hpr.pos h1
        have hmem1 := ih (N ⊔ Subgroup.zpowers (y * z ^ j.val)) hk hN₁ (u j) (huS j).2
          (mem_hyperFixed_sup_zpowers (huS j).1 hfix)
        refine (iSup₂_le fun F' hF' => ?_ : (⨆ (F' : Subgroup E)
          (_ : N ⊔ Subgroup.zpowers (y * z ^ j.val) ≤ F' ∧ F'.index = p),
            hyperFixed ρ F' ⊓ S) ≤ T) hmem1
        exact le_iSup₂_of_le F' ⟨le_trans le_sup_left hF'.1, hF'.2⟩ le_rfl
      have hv_mem : v ∈ T := by
        have hmem2 := ih (N ⊔ Subgroup.zpowers z) hk hN₂ v hvS.2
          (mem_hyperFixed_sup_zpowers hvS.1 hv)
        refine (iSup₂_le fun F' hF' => ?_ : (⨆ (F' : Subgroup E)
          (_ : N ⊔ Subgroup.zpowers z ≤ F' ∧ F'.index = p), hyperFixed ρ F' ⊓ S) ≤ T) hmem2
        exact le_iSup₂_of_le F' ⟨le_trans le_sup_left hF'.1, hF'.2⟩ le_rfl
      rw [hsum]
      exact T.add_mem (T.sum_mem fun j _ => hu_mem j) hv_mem

theorem mem_iSup_hyperFixed_top [Finite E] {p : ℕ} [Fact p.Prime] (hpF : (p : F) ≠ 0)
    (hcomm : ∀ a b : E, a * b = b * a) (hexp : ∀ a : E, a ^ p = 1) (ρ : E →* Module.End F M)
    (S : Submodule F M) (hS : ∀ (e : E), ∀ x ∈ S, ρ e x ∈ S) {k : ℕ} (hk : 1 ≤ k)
    (hcard : Nat.card E = p ^ k) {m : M} (hm : m ∈ S) :
    m ∈ ⨆ (F' : Subgroup E) (_ : F'.index = p), hyperFixed ρ F' ⊓ S := by
  have h := mem_iSup_hyperFixed hpF hcomm hexp ρ S hS k ⊥ hk (by rw [Subgroup.index_bot, hcard]) m
    hm (mem_hyperFixed.2 fun n hn => by rw [Subgroup.mem_bot.1 hn, map_one]; rfl)
  refine (iSup₂_le fun F' hF' => le_iSup₂_of_le F' hF'.2 le_rfl : (⨆ (F' : Subgroup E)
    (_ : (⊥ : Subgroup E) ≤ F' ∧ F'.index = p), hyperFixed ρ F' ⊓ S) ≤ ⨆ (F' : Subgroup E)
    (_ : F'.index = p), hyperFixed ρ F' ⊓ S) h

end Averaging

end CFSG.LieType.SeitzGeneration
