module

public import Mathlib.GroupTheory.Nilpotent
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.MinimalNormalPSubgroupIsElementaryAbelian

public section

namespace CFSG

variable {L Q : Type*} [Group L] [Group Q]

theorem exists_sylow_mem_le_centralizer_map [Finite L] {p : ℕ} [Fact p.Prime] (f : L →* Q)
    (hf : Function.Surjective f) {d : L}
    (hd : ∃ S : Sylow p L, d ∈ (S : Subgroup L) ∧ (S : Subgroup L) ≤ Subgroup.centralizer {d}) :
    ∃ S : Sylow p Q, f d ∈ (S : Subgroup Q) ∧ (S : Subgroup Q) ≤ Subgroup.centralizer {f d} := by
  obtain ⟨S, hdS, hSC⟩ := hd
  refine ⟨S.mapSurjective hf, ?_, ?_⟩
  · rw [Sylow.coe_mapSurjective]
    exact Subgroup.mem_map_of_mem f hdS
  · rw [Sylow.coe_mapSurjective, Subgroup.map_le_iff_le_comap]
    intro s hs
    have h := Subgroup.mem_centralizer_singleton_iff.mp (hSC hs)
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, h]

theorem orderOf_map_eq_of_isPGroup_ker {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hpq : p ≠ q) (f : L →* Q) (hker : IsPGroup q f.ker) {d : L} (hd : orderOf d = p) :
    orderOf (f d) = p := by
  have hdvd : orderOf (f d) ∣ p := hd ▸ orderOf_map_dvd f d
  refine ((Nat.dvd_prime hp.out).mp hdvd).resolve_left fun h1 => hpq ?_
  have hdk : d ∈ f.ker := MonoidHom.mem_ker.mpr (orderOf_eq_one_iff.mp h1)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hker) ⟨d, hdk⟩
  have hpk : p = q ^ k := hd.symm.trans ((Subgroup.orderOf_coe ⟨d, hdk⟩).trans hk)
  have hdvd' : p ∣ q ^ k := by rw [← hpk]
  exact (Nat.prime_dvd_prime_iff_eq hp.out hq.out).mp (hp.out.dvd_of_dvd_pow hdvd')

theorem zpowers_eq_inf_centralizer_of_card [Finite L] {p : ℕ} [Fact p.Prime] {S : Subgroup L}
    (hZ : Nat.card ↥(S ⊓ Subgroup.centralizer (S : Set L)) = p) {x : L} (hx : x ≠ 1)
    (hxS : x ∈ S) (hSx : S ≤ Subgroup.centralizer {x}) :
    Subgroup.zpowers x = S ⊓ Subgroup.centralizer (S : Set L) := by
  have hxC : x ∈ Subgroup.centralizer (S : Set L) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact Subgroup.mem_centralizer_singleton_iff.mp (hSx hs)
  have hle : Subgroup.zpowers x ≤ S ⊓ Subgroup.centralizer (S : Set L) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hxS, hxC⟩)
  have hdvd : Nat.card ↥(Subgroup.zpowers x) ∣ p := hZ ▸ Subgroup.card_dvd_of_le hle
  have hne : Nat.card ↥(Subgroup.zpowers x) ≠ 1 := by
    rw [Nat.card_zpowers]
    exact fun h => hx (orderOf_eq_one_iff.mp h)
  have hcard : Nat.card ↥(Subgroup.zpowers x) = p :=
    ((Nat.dvd_prime (Fact.out : p.Prime)).mp hdvd).resolve_left hne
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hZ, hcard])

theorem exists_map_conj_zpowers_eq [Finite L] {p : ℕ} [Fact p.Prime]
    (hZ : ∀ S : Sylow p L, Nat.card ↥((S : Subgroup L) ⊓ Subgroup.centralizer (S : Set L)) = p)
    {a b : L} (ha : a ≠ 1)
    (haS : ∃ S : Sylow p L, a ∈ (S : Subgroup L) ∧ (S : Subgroup L) ≤ Subgroup.centralizer {a})
    (hb : b ≠ 1)
    (hbS : ∃ S : Sylow p L, b ∈ (S : Subgroup L) ∧ (S : Subgroup L) ≤ Subgroup.centralizer {b}) :
    ∃ g : L, (Subgroup.zpowers a).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers b := by
  obtain ⟨Sa, haSa, hSaC⟩ := haS
  obtain ⟨Sb, hbSb, hSbC⟩ := hbS
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq L Sa Sb
  have hSb : (Sb : Subgroup L) = (Sa : Subgroup L).map (MulAut.conj g).toMonoidHom := by
    have h := congrArg (fun S : Sylow p L => (S : Subgroup L)) hg
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h
    rw [← h]
    rfl
  set c := (MulAut.conj g).toMonoidHom a with hc
  have hcSb : c ∈ (Sb : Subgroup L) := hSb ▸ Subgroup.mem_map_of_mem _ haSa
  have hSbc : (Sb : Subgroup L) ≤ Subgroup.centralizer {c} := by
    rw [hSb, Subgroup.map_le_iff_le_comap]
    intro s hs
    have h := Subgroup.mem_centralizer_singleton_iff.mp (hSaC hs)
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, hc, ← map_mul, ← map_mul, h]
  have hc1 : c ≠ 1 := fun h => ha ((MulAut.conj g).injective (h.trans (map_one _).symm))
  refine ⟨g, ?_⟩
  rw [MonoidHom.map_zpowers, ← hc, zpowers_eq_inf_centralizer_of_card (hZ Sb) hc1 hcSb hSbc,
    zpowers_eq_inf_centralizer_of_card (hZ Sb) hb hbSb hSbC]

theorem minimalNormal_le_isPGroup [Finite L] {p : ℕ} [Fact p.Prime] {M R : Subgroup L}
    (hM : M.Normal) (hR : R.Normal) (hRp : IsPGroup p R) (hMR : M ≤ R) (hM1 : M ≠ ⊥)
    (hmin : ∀ K : Subgroup L, K.Normal → K ≤ M → K = ⊥ ∨ K = M) :
    IsElementaryAbelian p M ∧ R ≤ Subgroup.centralizer (M : Set L) := by
  have hMp : IsPGroup p M := hRp.to_le hMR
  refine ⟨?_, ?_⟩
  · have : IsMinimalNormal M := ⟨fun K _ hK => hmin K inferInstance hK⟩
    exact Glauberman.minimalNormal_pSubgroup_isElementaryAbelian M hM1 hMp
  · have hRnil : Group.IsNilpotent R := hRp.isNilpotent
    have hMRn : (M.subgroupOf R).Normal := hM.subgroupOf R
    have hne : M.subgroupOf R ≠ ⊥ := by
      intro h
      rw [Subgroup.subgroupOf_eq_bot] at h
      exact hM1 (h.eq_bot_of_le hMR)
    obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
      (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
    have hyM : (y : L) ∈ M := Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hy).1
    have hyC : (y : L) ∈ Subgroup.centralizer (R : Set L) := by
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      have h := Subgroup.mem_center_iff.mp (Subgroup.mem_inf.mp hy).2 ⟨r, hr⟩
      exact congrArg Subtype.val h
    have hCn : (Subgroup.centralizer (R : Set L)).Normal := by
      constructor
      intro n hn g
      rw [Subgroup.mem_centralizer_iff] at hn ⊢
      intro r hr
      have h := hn (g⁻¹ * r * g) (by simpa using hR.conj_mem r hr g⁻¹)
      calc r * (g * n * g⁻¹) = g * ((g⁻¹ * r * g) * n) * g⁻¹ := by group
        _ = g * (n * (g⁻¹ * r * g)) * g⁻¹ := by rw [h]
        _ = g * n * g⁻¹ * r := by group
    have hN : (M ⊓ Subgroup.centralizer (R : Set L)).Normal := Subgroup.normal_inf_normal _ _
    rcases hmin _ hN inf_le_left with h | h
    · exfalso
      apply hy1
      have hyN : (y : L) ∈ M ⊓ Subgroup.centralizer (R : Set L) := Subgroup.mem_inf.mpr ⟨hyM, hyC⟩
      rw [h, Subgroup.mem_bot] at hyN
      exact Subtype.ext (Subtype.ext hyN)
    · rw [Subgroup.le_centralizer_iff]
      exact h ▸ inf_le_right

theorem isElementaryAbelian_of_minimalNormal [Finite L] {p : ℕ} [Fact p.Prime] {M : Subgroup L}
    (hM : M.Normal) (hMp : IsPGroup p M) (hM1 : M ≠ ⊥)
    (hmin : ∀ K : Subgroup L, K.Normal → K ≤ M → K = ⊥ ∨ K = M) :
    IsElementaryAbelian p M :=
  (minimalNormal_le_isPGroup hM hM hMp le_rfl hM1 hmin).1

end CFSG
