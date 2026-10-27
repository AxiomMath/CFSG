module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.Foundations.Basic
import CFSG.GroupTheory.LocalCores.PrimeSetCore
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas
import CFSG.FeitThompson.OddOrderTheorem

public section

open Subgroup

namespace CFSG.ABGLocalTools

section Defs

variable (p : ℕ) (H : Type*) [Group H]

@[expose] def IsPConstrained : Prop :=
  ∀ P : Subgroup H, IsSylowOf p P (Op_p'p p H) → centralizer (P : Set H) ≤ Op_p'p p H

@[expose] def PConstrainedWithin (K : Subgroup H) : Prop :=
  Op_p'p p H ≤ K ∧ IsPConstrained p H

variable {H} in
@[expose] noncomputable def normalizerPCoreModCentralizer (P : Subgroup H) : Subgroup H :=
  ((pCore p (normalizer (P : Set H) ⧸
      (centralizer (P : Set H)).subgroupOf (normalizer (P : Set H)))).comap
    (QuotientGroup.mk' ((centralizer (P : Set H)).subgroupOf (normalizer (P : Set H))))).map
    (normalizer (P : Set H)).subtype

@[expose] def IsPStable : Prop :=
  pCore p H ≠ ⊥ ∧
    ∀ P A : Subgroup H, P ≠ ⊥ → IsPGroup p P → (pPrimeCore p H ⊔ P).Normal →
      IsPGroup p A → A ≤ normalizer (P : Set H) → ⁅⁅P, A⁆, A⁆ = ⊥ →
        A ≤ normalizerPCoreModCentralizer p P

@[expose] def IsPStableWrt (R : Subgroup H) : Prop :=
  pCore p H ≠ ⊥ ∧ IsPGroup p R ∧ IsSylowOf p (R ⊓ Op_p'p p H) (Op_p'p p H) ∧
    ((∃ S : Sylow p H, R ≤ S ∧ (S : Subgroup H) ≤ normalizer (R : Set H)) ∨
      ∀ (K : Subgroup H) [K.Normal], pCore p (H ⧸ K) ≤ R.map (QuotientGroup.mk' K)) ∧
    ∀ P A : Subgroup H, P ≠ ⊥ → P ≤ R → (pPrimeCore p H ⊔ P).Normal → A ≤ R →
      ⁅⁅P, A⁆, A⁆ = ⊥ → A ≤ normalizerPCoreModCentralizer p P

end Defs

section Cores

variable {p : ℕ} {H : Type*} [Group H]

theorem pPrimeCore_le_Op_p'p : pPrimeCore p H ≤ Op_p'p p H := by
  intro x hx
  change QuotientGroup.mk' (pPrimeCore p H) x ∈ pCore p (H ⧸ pPrimeCore p H)
  rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff (N := pPrimeCore p H) x).mpr hx]
  exact one_mem _

theorem odd_card_oddCore [Finite H] : Odd (Nat.card (oddCore H)) := by
  have h := LocalCores.piCore_isPiSubgroup (G := H) {q : Nat.Primes | q.val ≠ 2}
  rw [← oddCore_eq_piCore] at h
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  exact h ⟨2, Nat.prime_two⟩ h2 rfl

theorem le_oddCore_of_normal {N : Subgroup H} (hN : N.Normal) (hodd : Odd (Nat.card N)) :
    N ≤ oddCore H :=
  le_sSup ⟨hN, hodd⟩

theorem isSolvable_sup_of_normal (N₁ N₂ : Subgroup H) [hN₁ : N₁.Normal] [N₂.Normal]
    [Group.IsSolvable N₁] [Group.IsSolvable N₂] :
    Group.IsSolvable (N₁ ⊔ N₂ : Subgroup H) := by
  let L : Subgroup H := N₁ ⊔ N₂
  let M : Subgroup L := N₁.subgroupOf L
  have hM : M.Normal := Subgroup.normal_subgroupOf
  have hMsolv : Group.IsSolvable M :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe
      (le_sup_left : N₁ ≤ L)).toMonoidHom) (Subgroup.subgroupOfEquivOfLe le_sup_left).injective
  let f : N₂ →* L ⧸ M :=
    (QuotientGroup.mk' M).comp (Subgroup.inclusion (le_sup_right : N₂ ≤ L))
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk'_surjective M y
    obtain ⟨a, ha, b, hb, rfl⟩ := (Subgroup.mem_sup_of_normal_left (s := N₁) (t := N₂)).mp hx
    refine ⟨⟨b, hb⟩, ?_⟩
    simp only [f, MonoidHom.comp_apply]
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    simpa [mul_assoc] using hN₁.conj_mem' a ha b
  have : Group.IsSolvable (L ⧸ M) := Group.isSolvable_of_surjective hf
  exact Group.isSolvable_of_subgroup_quotient M

theorem solvableRadical_isSolvable [Finite H] : Group.IsSolvable (solvableRadical H) := by
  classical
  obtain ⟨M, -, hM⟩ := Finite.exists_le_maximal
    (p := fun N : Subgroup H => N.Normal ∧ Group.IsSolvable N) (a := ⊥)
    ⟨inferInstance, inferInstance⟩
  have hge : ∀ N : Subgroup H, N.Normal ∧ Group.IsSolvable N → N ≤ M := by
    rintro N ⟨hN, hNs⟩
    have : M.Normal := hM.1.1
    have : Group.IsSolvable M := hM.1.2
    have h := hM.eq_of_le ⟨inferInstance, isSolvable_sup_of_normal M N⟩ le_sup_left
    rw [h]
    exact le_sup_right
  have heq : solvableRadical H = M := le_antisymm (sSup_le hge) (le_sSup hM.1)
  rw [heq]
  exact hM.1.2

theorem solvableRadical_normal : (solvableRadical H).Normal :=
  Subgroup.sSup_normal _ fun _ hN => hN.1

theorem Op_p'p_le_oddCore [Finite H] [Fact p.Prime] (hp : p ≠ 2)
    (h : pPrimeCore p H ≤ oddCore H) : Op_p'p p H ≤ oddCore H := by
  apply le_oddCore_of_normal inferInstance
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Op_p'p p H) 2 h2
  have hxo : orderOf (x : H) = 2 := by rw [Subgroup.orderOf_coe, hx]
  have hxM : (x : H) ∈ pPrimeCore p H := by
    have hcop : Nat.Coprime p (Nat.card (zpowers (x : H))) := by
      rw [Nat.card_zpowers, hxo]
      exact (Nat.coprime_primes (Fact.out) Nat.prime_two).mpr hp
    exact le_pPrimeCore_of_le_Op_p'p_of_coprime (G := H) p (zpowers_le.mpr x.2) hcop
      (mem_zpowers _)
  have hdvd : orderOf (x : H) ∣ Nat.card (oddCore H) := Subgroup.orderOf_dvd_natCard _ (h hxM)
  rw [hxo] at hdvd
  exact (Nat.not_even_iff_odd.mpr odd_card_oddCore) (even_iff_two_dvd.mpr hdvd)

theorem Op_p'p_le_solvableRadical [Finite H] [Fact p.Prime]
    (h : pPrimeCore p H ≤ solvableRadical H) : Op_p'p p H ≤ solvableRadical H := by
  apply le_sSup
  refine ⟨inferInstance, ?_⟩
  have hME : pPrimeCore p H ≤ Op_p'p p H := pPrimeCore_le_Op_p'p
  have : Group.IsSolvable (solvableRadical H) := solvableRadical_isSolvable
  have hMsolv : Group.IsSolvable ((pPrimeCore p H).subgroupOf (Op_p'p p H)) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.inclusion h).comp (Subgroup.subgroupOfEquivOfLe hME).toMonoidHom)
      ((Subgroup.inclusion_injective h).comp (Subgroup.subgroupOfEquivOfLe hME).injective)
  let g : Op_p'p p H →* pCore p (H ⧸ pPrimeCore p H) :=
    ((QuotientGroup.mk' (pPrimeCore p H)).comp (Op_p'p p H).subtype).codRestrict _
      (fun x => x.2)
  have hg : g.ker ≤ ((pPrimeCore p H).subgroupOf (Op_p'p p H)).subtype.range := by
    intro x hx
    rw [Subgroup.range_subtype]
    have hx1 : QuotientGroup.mk' (pPrimeCore p H) (x : H) = 1 := by
      have := congrArg Subtype.val ((MonoidHom.mem_ker).mp hx)
      exact this
    rw [Subgroup.mem_subgroupOf]
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx1
    exact hx1
  have : Group.IsSolvable (pCore p (H ⧸ pPrimeCore p H)) := by
    have : Group.IsNilpotent (pCore p (H ⧸ pPrimeCore p H)) := pCore_isPGroup.isNilpotent
    infer_instance
  exact Group.isSolvable_of_ker_le_range _ g hg

theorem isPConstrained_of_isSolvable [Finite H] [Fact p.Prime] (hsolv : Group.IsSolvable H) :
    IsPConstrained p H := by
  rintro _ ⟨T, rfl⟩
  exact centralizer_sylow_subgroup_le_op_p_prime_p_of_solvable hsolv p T

theorem pConstrainedWithin_oddCore_iff [Finite H] [Fact p.Prime] (hp : p ≠ 2) :
    PConstrainedWithin p H (oddCore H) ↔ IsPConstrained p H ∧ pPrimeCore p H ≤ oddCore H :=
  ⟨fun h => ⟨h.2, pPrimeCore_le_Op_p'p.trans h.1⟩, fun h => ⟨Op_p'p_le_oddCore hp h.2, h.1⟩⟩

theorem pConstrainedWithin_solvableRadical_iff [Finite H] [Fact p.Prime] :
    PConstrainedWithin p H (solvableRadical H) ↔
      IsPConstrained p H ∧ pPrimeCore p H ≤ solvableRadical H :=
  ⟨fun h => ⟨h.2, pPrimeCore_le_Op_p'p.trans h.1⟩, fun h => ⟨Op_p'p_le_solvableRadical h.2, h.1⟩⟩

end Cores

section Lemma61

variable {G : Type*} [Group G]

theorem le_normalizer_map_subtype (K : Subgroup G) (N : Subgroup K) [N.Normal] :
    K ≤ normalizer ((N.map K.subtype : Subgroup G) : Set G) := by
  have h := Subgroup.le_normalizer_map (H := N) K.subtype
  rw [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  exact h

theorem two_group_centralizes_sylow_iff [Finite G] {p : ℕ} [Fact p.Prime] {K S P : Subgroup G}
    (hK : Odd (Nat.card K)) (hS : IsPGroup 2 S) (_hSK : S ≤ normalizer (K : Set G))
    (hP : IsSylowOf p P K) (hSP : S ≤ normalizer (P : Set G)) :
    S ≤ centralizer (P : Set G) ↔
      S ≤ centralizer ((P ⊓ (Op_p'p p K).map K.subtype : Subgroup G) : Set G) := by
  set E : Subgroup G := (Op_p'p p K).map K.subtype with hE
  set Q : Subgroup G := P ⊓ E with hQ
  constructor
  · intro h
    exact h.trans (Subgroup.centralizer_le (fun x hx => (inf_le_left : Q ≤ P) hx))
  intro hSQ
  have hEK : E ≤ K := Subgroup.map_subtype_le _
  have hKE : K ≤ normalizer (E : Set G) := le_normalizer_map_subtype K _
  have hPK : P ≤ K := hP.le
  have hQK : Q ≤ K := inf_le_left.trans hPK
  have hcent : ∀ c ∈ K, c ∈ centralizer (Q : Set G) → c ∈ E := by
    intro c hcK hcQ
    have hsolv : Group.IsSolvable K := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hK
    have hQsyl : IsSylowOf p Q E := hP.inf_of_le_normalizer hEK hKE
    have hQ' : IsSylowOf p (Q.subgroupOf K) (Op_p'p p K) := by
      rw [← isSylowOf_map_subtype_iff K, Subgroup.subgroupOf_map_subtype,
        inf_eq_left.mpr hQK]
      exact hQsyl
    have hle := isPConstrained_of_isSolvable hsolv _ hQ'
    have hmem : (⟨c, hcK⟩ : K) ∈ centralizer ((Q.subgroupOf K : Subgroup K) : Set K) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp hcQ) q hq
    exact Subgroup.mem_map_of_mem K.subtype (hle hmem)
  have hPQ : P ≤ normalizer (Q : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx, hKE (hPK hx)⟩
  intro s hs
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hsQ : ∀ q ∈ Q, s * q = q * s := fun q hq =>
    ((Subgroup.mem_centralizer_iff.mp (hSQ hs)) q hq).symm
  have hyP : s * x * s⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hSP hs) x).mp hx
  set c : G := x⁻¹ * (s * x * s⁻¹) with hc
  have hcP : c ∈ P := P.mul_mem (P.inv_mem hx) hyP
  have hcQ : c ∈ Q := by
    refine ⟨hcP, hcent c (hPK hcP) ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hq' : x * q * x⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hPQ hx) q).mp hq
    have e1 : s⁻¹ * q * s = q := by
      rw [mul_assoc, ← hsQ q hq, ← mul_assoc, inv_mul_cancel, one_mul]
    have e2 : s * (x * q * x⁻¹) * s⁻¹ = x * q * x⁻¹ := by
      rw [hsQ _ hq', mul_assoc, mul_inv_cancel, mul_one]
    have key : c * q * c⁻¹ = q := by
      calc c * q * c⁻¹ = x⁻¹ * (s * (x * (s⁻¹ * q * s) * x⁻¹) * s⁻¹) * x := by
            rw [hc]; group
        _ = x⁻¹ * (s * (x * q * x⁻¹) * s⁻¹) * x := by rw [e1]
        _ = x⁻¹ * (x * q * x⁻¹) * x := by rw [e2]
        _ = q := by group
    calc q * c = c * q * c⁻¹ * c := by rw [key]
      _ = c * q := by group
  have hsc : s * c = c * s := hsQ c hcQ
  have hxc : x * c = s * x * s⁻¹ := by rw [hc]; group
  have hpow : ∀ n : ℕ, s ^ n * x * (s ^ n)⁻¹ = x * c ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hcn : s * c ^ n * s⁻¹ = c ^ n := by
        rw [(Commute.pow_right hsc n).eq, mul_assoc, mul_inv_cancel, mul_one]
      calc s ^ (n + 1) * x * (s ^ (n + 1))⁻¹ = s * (s ^ n * x * (s ^ n)⁻¹) * s⁻¹ := by
            rw [pow_succ']; group
        _ = (s * x * s⁻¹) * (s * c ^ n * s⁻¹) := by rw [ih]; group
        _ = x * c ^ (n + 1) := by rw [hcn, pow_succ', ← mul_assoc, hxc]
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hS ⟨s, hs⟩
  have hsk : s ^ 2 ^ k = 1 := by
    have hso : orderOf s = 2 ^ k := by rw [← Subgroup.orderOf_mk s hs]; exact hk
    rw [← hso]
    exact pow_orderOf_eq_one s
  have hck : c ^ 2 ^ k = 1 := by
    have := hpow (2 ^ k)
    rw [hsk, one_mul, inv_one, mul_one] at this
    exact (mul_eq_left.mp this.symm)
  have hc1 : c = 1 := by
    have h1 : orderOf c ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hck
    have h2 : orderOf c ∣ Nat.card K := Subgroup.orderOf_dvd_natCard K (hPK hcP)
    have hcop : Nat.Coprime (2 ^ k) (Nat.card K) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hK)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  have hy : s * x * s⁻¹ = x := by
    have : x⁻¹ * (s * x * s⁻¹) = 1 := hc1
    rw [inv_mul_eq_one] at this
    exact this.symm
  calc x * s = s * x * s⁻¹ * s := by rw [hy]
    _ = s * x := by group

end Lemma61

end CFSG.ABGLocalTools
