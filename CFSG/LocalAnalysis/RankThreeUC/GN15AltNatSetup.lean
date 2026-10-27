module

public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56.BridgeAbstract

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.B1Red CFSG.RankThree.PartTwo CFSG.QuasithinUnique
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56

structure AltNatSetup {V : Type} [CommGroup V] (H L A : Subgroup (MulAut V)) : Prop where
  lp : ∀ x ∈ L, ∀ q ∈ pCoreOf 2 H, x * q = q * x
  ker : H ⊓ centSub (fixV (pCoreOf 2 H)) = pCoreOf 2 H
  dec : ∀ x ∈ H, ∃ l ∈ L, ∃ a ∈ A, x = l * a
  an : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L
  cl : ∀ a ∈ A, (∀ l ∈ L, a * l = l * a) → a ∈ pCoreOf 2 H

theorem altNatSetup {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {H L A : Subgroup (MulAut V)} {n : ℕ} (hn : 5 ≤ n) (e : ↥L ≃* alternatingGroup (Fin n))
    (hLH : L ≤ H) (hLn : ∀ h ∈ H, ∀ l ∈ L, h * l * h⁻¹ ∈ L) (hHA : H ≤ L ⊔ A) (hAH : A ≤ H)
    (hA2 : ∀ a ∈ A, a * a = 1) : AltNatSetup H L A := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := pCoreOf 2 H with hPdef
  have hP2 : IsPGroup 2 ↥P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hPH : P ≤ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H
  have hsimple : IsSimpleGroup ↥L := by
    have : IsSimpleGroup (alternatingGroup (Fin n)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; omega)
    exact MulEquiv.isSimpleGroup e
  have hLP1 : L ⊓ P = ⊥ := by
    have hnorm : ((L ⊓ P).subgroupOf L).Normal :=
      (Subgroup.normal_subgroupOf_iff inf_le_left).2 fun y l hy hl =>
        ⟨L.mul_mem (L.mul_mem hl hy.1) (L.inv_mem hl), conj_mem_pCoreOf (hLH hl) hy.2⟩
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal ↥L _ _ _ hnorm with h | h
    · refine eq_bot_iff.2 fun x hx => ?_
      have hx' : (⟨x, hx.1⟩ : ↥L) ∈ (L ⊓ P).subgroupOf L := hx
      rw [h, Subgroup.mem_bot] at hx'
      exact (Subgroup.mem_bot).2 (congrArg Subtype.val hx')
    · exfalso
      have hLP : L ≤ P := fun x hx => by
        have hx' : (⟨x, hx⟩ : ↥L) ∈ (L ⊓ P).subgroupOf L := by rw [h]; trivial
        exact hx'.2
      have h2 : IsPGroup 2 ↥L := hP2.to_le hLP
      exact alt_not_two_group (by omega) (h2.of_surjective e.toMonoidHom e.surjective)
  have hLP : ∀ x ∈ L, ∀ q ∈ P, x * q = q * x := by
    intro x hx q hq
    have h1 : x * q * x⁻¹ * q⁻¹ ∈ L := by
      have := L.mul_mem hx (hLn q (hPH hq) x⁻¹ (L.inv_mem hx))
      simpa [mul_assoc] using this
    have h2 : x * q * x⁻¹ * q⁻¹ ∈ P :=
      P.mul_mem (conj_mem_pCoreOf (hLH hx) hq) (P.inv_mem hq)
    have h3 : x * q * x⁻¹ * q⁻¹ ∈ L ⊓ P := ⟨h1, h2⟩
    rw [hLP1, Subgroup.mem_bot] at h3
    calc x * q = (x * q * x⁻¹ * q⁻¹) * q * x := by group
      _ = q * x := by rw [h3]; group
  have hAn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L := fun a ha l hl => hLn a (hAH ha) l hl
  have hAn' : A ≤ Subgroup.normalizer (L : Set (MulAut V)) :=
    le_normalizer_of_conj fun a ha l hl => hLn a (hAH ha) l hl
  have hdec : ∀ x ∈ H, ∃ l ∈ L, ∃ a ∈ A, x = l * a := fun x hx =>
    exists_mul_of_sup hAn' (hHA hx)
  have hsq : ∀ x ∈ H, x ^ 2 ∈ L := by
    intro x hx
    obtain ⟨l, hl, a, ha, rfl⟩ := hdec x hx
    have ha1 : a * a = 1 := hA2 a ha
    have : (l * a) ^ 2 = l * (a * l * a⁻¹) * (a * a) := by rw [pow_two]; simp [mul_assoc]
    rw [this, ha1, mul_one]
    exact L.mul_mem hl (hAn a ha l hl)
  have hD : ∀ x ∈ H, Odd (orderOf x) → x ∈ L := by
    intro x hx ho
    obtain ⟨m, hm⟩ := ho
    have hx1 : x ^ (2 * m + 1) = 1 := hm ▸ pow_orderOf_eq_one x
    have : (x ^ 2) ^ (m + 1) = x := by
      rw [← pow_mul, show 2 * (m + 1) = (2 * m + 1) + 1 by ring, pow_succ, hx1, one_mul]
    exact this ▸ L.pow_mem (hsq x hx) (m + 1)
  have hker : H ⊓ centSub (fixV P) = P := kernel_eq_pCoreOf hV hD hLP
  have hZ : ∀ z : ↥L, (∀ l : ↥L, z * l = l * z) → z = 1 := by
    intro z hz
    have hc : e z ∈ Subgroup.center (alternatingGroup (Fin n)) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have := congrArg e (hz (e.symm y))
      simpa using this.symm
    rw [alternatingGroup.center_eq_bot (by rw [Nat.card_fin]; omega), Subgroup.mem_bot] at hc
    exact e.injective (by simpa using hc)
  have hcl : ∀ a ∈ A, (∀ l ∈ L, a * l = l * a) → a ∈ P := by
    intro a ha hcomm
    let N : Subgroup (MulAut V) := H ⊓ Subgroup.centralizer (L : Set (MulAut V))
    have hNH : N ≤ H := inf_le_left
    have hconjN : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N := by
      intro h hh n hn
      refine ⟨H.mul_mem (H.mul_mem hh hn.1) (H.inv_mem hh),
        Subgroup.mem_centralizer_iff.2 fun l hl => ?_⟩
      have hl' : h⁻¹ * l * h ∈ L := by
        have := hLn h⁻¹ (H.inv_mem hh) l hl
        simpa using this
      have h1 : (h⁻¹ * l * h) * n = n * (h⁻¹ * l * h) := Subgroup.mem_centralizer_iff.1 hn.2 _ hl'
      calc l * (h * n * h⁻¹) = h * ((h⁻¹ * l * h) * n) * h⁻¹ := by group
        _ = h * (n * (h⁻¹ * l * h)) * h⁻¹ := by rw [h1]
        _ = h * n * h⁻¹ * l := by group
    have hNnorm : H ≤ Subgroup.normalizer (N : Set (MulAut V)) := by
      intro h hh
      rw [Subgroup.mem_normalizer_iff]
      intro g
      constructor
      · intro hg
        exact hconjN h hh g hg
      · intro hg
        have := hconjN h⁻¹ (H.inv_mem hh) _ hg
        simpa [mul_assoc] using this
    have hN2 : ∀ h ∈ N, h * h = 1 := by
      intro h hn
      obtain ⟨l, hl, a', ha', hh'⟩ := hdec h hn.1
      have hmem : h * h ∈ L := by
        have : h * h = l * (a' * l * a'⁻¹) * (a' * a') := by
          rw [hh']; simp [mul_assoc]
        rw [this, hA2 a' ha', mul_one]
        exact L.mul_mem hl (hAn a' ha' l hl)
      have hmemN : h * h ∈ N := N.mul_mem hn hn
      have := hZ ⟨h * h, hmem⟩ fun l => Subtype.ext (by
        exact ((Subgroup.mem_centralizer_iff.1 hmemN.2) l l.2).symm)
      exact congrArg Subtype.val this
    have hNp : IsPGroup 2 ↥N := fun h => ⟨1, by
      rw [pow_one]; exact Subtype.ext (by simpa [pow_two] using hN2 h.1 h.2)⟩
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hNH hNnorm hNp
      ⟨hAH ha, Subgroup.mem_centralizer_iff.2 fun l hl => (hcomm l hl).symm⟩
  exact ⟨hLP, hker, hdec, hAn, hcl⟩

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
