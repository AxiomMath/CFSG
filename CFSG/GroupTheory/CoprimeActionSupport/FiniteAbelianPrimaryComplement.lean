module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.GroupTheory.CoprimeActionSupport.FiniteAbelianPrimaryComplement

variable {G : Type} [Group G]

theorem exists_complement {p : ℕ} (hp : p.Prime) [Finite G] {B : Subgroup G}
    (hB : IsMulCommutative B) :
    ∃ A : Subgroup G, A ≤ B ∧ Nat.Coprime (Nat.card A) p ∧
      CFSG.Open.pCoreOf p B ⊔ A = B ∧
      Nat.Coprime (Nat.card (CFSG.Open.pCoreOf p B)) (Nat.card A) := by
  have pCore_isPGroup' (p : ℕ) (H : Type) [Group H] :
      IsPGroup p (CFSG.Open.pCore p H) := by
    have : CFSG.Open.pCore p H = CFSG.pCore p H := rfl
    rw [this]
    exact CFSG.pCore_isPGroup
  have mem_pCoreOf {p : ℕ} (hp : p.Prime) [Finite G] {B : Subgroup G}
      (hB : IsMulCommutative B) {x : G} (hx : x ∈ B) {n : ℕ} (hn : x ^ (p ^ n) = 1) :
      x ∈ CFSG.Open.pCoreOf p B := by
    set y : B := ⟨x, hx⟩ with hy
    have hyn : y ^ (p ^ n) = 1 := Subtype.ext (by simpa using hn)
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hyn)
    haveI : (Subgroup.zpowers y).Normal :=
      ⟨fun m hm g => by
        have : g * m = m * g := hB.is_comm.comm g m
        rwa [show g * m * g⁻¹ = m by rw [this, mul_assoc, mul_inv_cancel, mul_one]]⟩
    have hP : IsPGroup p (Subgroup.zpowers y) :=
      IsPGroup.of_card (by rw [Nat.card_zpowers, hk])
    have hle : Subgroup.zpowers y ≤ CFSG.Open.pCore p B :=
      le_sSup ⟨inferInstance, hP⟩
    exact ⟨y, hle (Subgroup.mem_zpowers y), rfl⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hcomm : ∀ a ∈ B, ∀ b ∈ B, Commute a b := fun a ha b hb =>
    congrArg Subtype.val (hB.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  let A : Subgroup G :=
    { carrier := {b | b ∈ B ∧ Nat.Coprime (orderOf b) p}
      one_mem' := ⟨B.one_mem, by simp⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨B.mul_mem ha hb, ?_⟩
        have h1 : orderOf (a * b) ∣ orderOf a * orderOf b :=
          ((hcomm a ha b hb).orderOf_mul_dvd_lcm).trans (Nat.lcm_dvd_mul _ _)
        exact (Nat.Coprime.mul_left ha' hb').coprime_dvd_left h1
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        exact ⟨B.inv_mem ha, by simpa using ha'⟩ }
  have hAB : A ≤ B := fun b hb => hb.1
  have hAcop : Nat.Coprime (Nat.card A) p := by
    refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 fun hdvd => ?_)
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := A) p hdvd
    have h1 : orderOf (x : G) = p := by rw [Subgroup.orderOf_coe]; exact hx
    have h2 := x.2.2
    rw [h1] at h2
    simp [Nat.coprime_self] at h2
    exact hp.one_lt.ne' h2
  have hPp : IsPGroup p (CFSG.Open.pCoreOf p B) := (pCore_isPGroup' p B).map _
  have hPB : CFSG.Open.pCoreOf p B ≤ B := Subgroup.map_subtype_le _
  refine ⟨A, hAB, hAcop, le_antisymm (sup_le hPB hAB) ?_, ?_⟩
  · intro b hb
    obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd
      (orderOf_pos (⟨b, hb⟩ : B)).ne' p hp.ne_one
    have hn' : orderOf b = p ^ a * m := by rw [← hn, Subgroup.orderOf_mk]
    have hmc : Nat.Coprime m p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hm).symm
    have hcop : IsCoprime ((p ^ a : ℕ) : ℤ) (m : ℤ) :=
      Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp).2 hm))
    obtain ⟨u, v, huv⟩ := hcop
    have hx : b ^ m ∈ CFSG.Open.pCoreOf p B :=
      mem_pCoreOf hp hB (B.pow_mem hb m) (n := a) (by
        rw [← pow_mul, mul_comm, ← hn']; exact pow_orderOf_eq_one b)
    have hy : b ^ (p ^ a) ∈ A := by
      refine ⟨B.pow_mem hb _, ?_⟩
      have : (b ^ (p ^ a)) ^ m = 1 := by
        rw [← pow_mul, ← hn']; exact pow_orderOf_eq_one b
      exact hmc.coprime_dvd_left (orderOf_dvd_of_pow_eq_one this)
    have hb' : b = (b ^ m) ^ v * (b ^ (p ^ a)) ^ u := by
      have h1 : (b ^ m) ^ v = b ^ ((m : ℤ) * v) := by rw [← zpow_natCast, ← zpow_mul]
      have h2 : (b ^ (p ^ a)) ^ u = b ^(((p ^ a : ℕ) : ℤ) * u) := by
        rw [← zpow_natCast b (p ^ a), ← zpow_mul]
      rw [h1, h2, ← zpow_add]
      have : (m : ℤ) * v + ((p ^ a : ℕ) : ℤ) * u = 1 := by linarith
      rw [this, zpow_one]
    rw [hb']
    exact Subgroup.mul_mem_sup (Subgroup.zpow_mem _ hx v) (Subgroup.zpow_mem _ hy u)
  · obtain ⟨k, hk⟩ := hPp.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_left k hAcop.symm

end CFSG.GroupTheory.CoprimeActionSupport.FiniteAbelianPrimaryComplement
