module

public import CFSG.CGT.Timmesfeld75.O2Core
public import CFSG.CGT.Timmesfeld75.CentralQuotient
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

section CentralKernel

variable {H H' : Type*} [Group H] [Group H']

theorem IsWC.map_of_ker_le_center {S : Subgroup H} (hS : IsWC S) (φ : H →* H')
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center H) (hSker : S ⊓ φ.ker = ⊥) :
    IsWC (S.map φ) := by
  have hSb := isElemAbelian_map_of_hom hS.1 φ
  refine ⟨hSb, fun tb htb htb1 => ⟨fun x hx => ?_, fun gb hgb => ?_⟩⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact elemAbelian_mul_comm hSb htb hx
  · obtain ⟨g, rfl⟩ := hφ gb
    obtain ⟨t, ht, rfl⟩ := htb
    have ht1 : t ≠ 1 := fun h => htb1 (by rw [h, map_one])
    have hcent : conjSubgroup g S ≤ Subgroup.centralizer ({t} : Set H) := by
      intro u hu
      have hu' : φ u ∈ conjSubgroup (φ g) (S.map φ) := by
        rw [← map_conjSubgroup]
        exact Subgroup.mem_map_of_mem _ hu
      have hc := Subgroup.mem_centralizer_iff.1 (hgb hu') (φ t) (Set.mem_singleton _)
      have hz : ⁅u, t⁆ ∈ φ.ker := by
        rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact hc.symm
      have hzc : ⁅u, t⁆ ∈ Subgroup.center H := hker hz
      have h1 : u * t * u⁻¹ = ⁅u, t⁆ * t := by simp only [commutatorElement_def]; group
      have hzt : ⁅u, t⁆ * t ∈ conjSubgroup u S := by
        rw [← h1, mem_conjSubgroup]
        simpa [mul_assoc] using ht
      have hzt1 : ⁅u, t⁆ * t ≠ 1 := by
        rw [← h1]
        intro h
        apply ht1
        have : t = u⁻¹ * (u * t * u⁻¹) * u := by group
        rw [this, h]
        group
      have hSle : conjSubgroup u⁻¹ (conjSubgroup u S) ≤
          Subgroup.centralizer ({⁅u, t⁆ * t} : Set H) := by
        rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
        intro s hs
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
        have hcs : ⁅u, t⁆ * s = s * ⁅u, t⁆ := (Subgroup.mem_center_iff.1 hzc s).symm
        have hts : t * s = s * t := elemAbelian_mul_comm hS.1 ht hs
        calc ⁅u, t⁆ * t * s = ⁅u, t⁆ * (t * s) := mul_assoc _ _ _
          _ = ⁅u, t⁆ * (s * t) := by rw [hts]
          _ = (⁅u, t⁆ * s) * t := (mul_assoc _ _ _).symm
          _ = (s * ⁅u, t⁆) * t := by rw [hcs]
          _ = s * (⁅u, t⁆ * t) := mul_assoc _ _ _
      have hSu : conjSubgroup u⁻¹ (conjSubgroup u S) = conjSubgroup u S :=
        ((hS.conj u).2 (⁅u, t⁆ * t) hzt hzt1).2 u⁻¹ hSle
      rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one] at hSu
      have hztS : ⁅u, t⁆ * t ∈ S := by
        rw [hSu]
        exact hzt
      have hzS : ⁅u, t⁆ ∈ S := by simpa using S.mul_mem hztS (S.inv_mem ht)
      have hz1 : ⁅u, t⁆ = 1 := by
        have h3 : ⁅u, t⁆ ∈ S ⊓ φ.ker := ⟨hzS, hz⟩
        rw [hSker, Subgroup.mem_bot] at h3
        exact h3
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact (commutatorElement_eq_one_iff_mul_comm.1 hz1).symm
    have hconj := (hS.2 t ht ht1).2 g hcent
    rw [← map_conjSubgroup, hconj]

theorem IsWC.map_quotient_central_of_inf_eq_bot {S : Subgroup H} (hS : IsWC S) (Z : Subgroup H)
    [Z.Normal] (hZc : Z ≤ Subgroup.center H) (hSZ : S ⊓ Z = ⊥) :
    IsWC (S.map (QuotientGroup.mk' Z)) :=
  hS.map_of_ker_le_center _ (QuotientGroup.mk'_surjective Z) (by rwa [QuotientGroup.ker_mk'])
    (by rwa [QuotientGroup.ker_mk'])

end CentralKernel

section Claims

variable {K : Type*} [Group K] [Finite K]

theorem mem_of_mem_sup_normalClosureInf_of_mem_conj {T : Subgroup K} (hT : IsWC T) {a h : K}
    (ha : a ∈ T ⊔ normalClosureInf T (CFSG.pCore 2 K)) (hah : a ∈ conjSubgroup h T)
    (ha0 : a ∉ normalClosureInf T (CFSG.pCore 2 K)) : a ∈ T := by
  have hN2 : IsPGroup 2 (CFSG.pCore 2 K) := CFSG.pCore_isPGroup
  have hN₀N : normalClosureInf T (CFSG.pCore 2 K) ≤ CFSG.pCore 2 K := normalClosureInf_le T
  by_cases hTN : T ⊓ CFSG.pCore 2 K = ⊥
  · rw [normalClosureInf_eq_bot_of_inf_eq_bot hTN, sup_bot_eq] at ha
    exact ha
  · obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hTN
    have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
    obtain ⟨b, hb, n', hn', rfl⟩ := Subgroup.mem_sup_of_normal_right.1 ha
    by_contra haT
    have hb0 : b ∉ normalClosureInf T (CFSG.pCore 2 K) := fun hb0 =>
      ha0 (Subgroup.mul_mem _ hb0 hn')
    have hTh : conjSubgroup h T ≠ T := fun heq => haT (heq ▸ hah)
    have hbot : T ⊓ conjSubgroup h T = ⊥ := hT.inf_conj_eq_bot hTh
    have hN₀ab := isElemAbelian_normalClosureInf hT hN2
    have hbC : ∀ u ∈ normalClosureInf T (CFSG.pCore 2 K), b * u = u * b := by
      intro u hu
      have huN : u ∈ CFSG.pCore 2 K := hN₀N hu
      have h1 : ⁅b, u⁆ ∈ T := by
        rw [← commutatorElement_inv u b]
        exact T.inv_mem (comm_mem_of_mem_normalizer (le_normalizer_of_normal_pGroup hT hN2 huN) hb)
      have h2 : ⁅b * n', u⁆ ∈ conjSubgroup h T := by
        rw [← commutatorElement_inv u (b * n')]
        exact (conjSubgroup h T).inv_mem (comm_mem_of_mem_normalizer
          (le_normalizer_of_normal_pGroup (hT.conj h) hN2 huN) hah)
      have hcomm : n' * u = u * n' := elemAbelian_mul_comm hN₀ab hn' hu
      have h3 : ⁅b * n', u⁆ = ⁅b, u⁆ := by
        have h4 : n' * u * n'⁻¹ = u := by rw [hcomm]; group
        calc ⁅b * n', u⁆ = b * (n' * u * n'⁻¹) * b⁻¹ * u⁻¹ := by
              simp only [commutatorElement_def]; group
          _ = ⁅b, u⁆ := by rw [h4]; simp only [commutatorElement_def]
      rw [h3] at h2
      have h5 : ⁅b, u⁆ ∈ T ⊓ conjSubgroup h T := ⟨h1, h2⟩
      rw [hbot, Subgroup.mem_bot] at h5
      exact commutatorElement_eq_one_iff_mul_comm.1 h5
    have hconjC : ∀ g : K, ∀ u ∈ normalClosureInf T (CFSG.pCore 2 K),
        (g * b * g⁻¹) * u = u * (g * b * g⁻¹) := by
      intro g u hu
      have hu' : g⁻¹ * u * g ∈ normalClosureInf T (CFSG.pCore 2 K) := by
        simpa using (normalClosureInf_normal T (CFSG.pCore 2 K)).conj_mem u hu g⁻¹
      have h := hbC _ hu'
      calc g * b * g⁻¹ * u = g * (b * (g⁻¹ * u * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * u * g) * b) * g⁻¹ := by rw [h]
        _ = u * (g * b * g⁻¹) := by group
    have hnorm : ∀ g : K, g * b * g⁻¹ ∈ Subgroup.normalizer (T : Set K) := fun g =>
      hT.centralizer_le_normalizer hy.1 hy1'
        (Subgroup.mem_centralizer_singleton_iff.2 (hconjC g y (inf_le_normalClosureInf T _ hy)))
    have hbN : b ∈ CFSG.pCore 2 K := mem_pCore_of_conj_mem_normalizer hT.1 hb hnorm
    exact hb0 (inf_le_normalClosureInf T _ ⟨hb, hbN⟩)

theorem isWC_map_normalClosureInf {T : Subgroup K} (hT : IsWC T) :
    IsWC (T.map (QuotientGroup.mk' (normalClosureInf T (CFSG.pCore 2 K)))) := by
  have hN2 : IsPGroup 2 (CFSG.pCore 2 K) := CFSG.pCore_isPGroup
  have hN₀2 : IsPGroup 2 (normalClosureInf T (CFSG.pCore 2 K)) :=
    hN2.to_le (normalClosureInf_le T)
  have hTb := isElemAbelian_map_of_hom hT.1
    (QuotientGroup.mk' (normalClosureInf T (CFSG.pCore 2 K)))
  refine ⟨hTb, fun tb htb htb1 => ⟨fun x hx => ?_, fun gb hgb => ?_⟩⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact elemAbelian_mul_comm hTb htb hx
  · obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective gb
    obtain ⟨b, hb, rfl⟩ := htb
    have hb0 : b ∉ normalClosureInf T (CFSG.pCore 2 K) := fun h0 =>
      htb1 ((QuotientGroup.eq_one_iff b).2 h0)
    have hb1 : b ≠ 1 := fun h => hb0 (h ▸ Subgroup.one_mem _)
    have hcomm : ∀ x ∈ conjSubgroup g T, ⁅x, b⁆ ∈ normalClosureInf T (CFSG.pCore 2 K) := by
      intro x hx
      have hxm : QuotientGroup.mk' (normalClosureInf T (CFSG.pCore 2 K)) x ∈
          conjSubgroup (QuotientGroup.mk' (normalClosureInf T (CFSG.pCore 2 K)) g)
            (T.map (QuotientGroup.mk' (normalClosureInf T (CFSG.pCore 2 K)))) := by
        rw [← map_conjSubgroup]
        exact Subgroup.mem_map_of_mem _ hx
      have hc := Subgroup.mem_centralizer_iff.1 (hgb hxm)
        (QuotientGroup.mk' (normalClosureInf T (CFSG.pCore 2 K)) b) (Set.mem_singleton _)
      have h1 : QuotientGroup.mk' (normalClosureInf T (CFSG.pCore 2 K)) ⁅x, b⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact hc.symm
      exact (QuotientGroup.eq_one_iff _).1 h1
    have hbN : b ∈ Subgroup.normalizer (conjSubgroup g T : Set K) := by
      refine mem_normalizer_of_commutator_mem (hT.conj g) hN₀2 fun x hx => ?_
      rw [← commutatorElement_inv x b]
      exact Subgroup.inv_mem _ (hcomm x hx)
    have hxT : ∀ x ∈ conjSubgroup g T, ⁅x, b⁆ ∈ T := by
      intro x hx
      have hcsup : ⁅x, b⁆ * b ∈ T ⊔ normalClosureInf T (CFSG.pCore 2 K) :=
        Subgroup.mul_mem _ (Subgroup.mem_sup_right (hcomm x hx)) (Subgroup.mem_sup_left hb)
      have hcconj : ⁅x, b⁆ * b ∈ conjSubgroup x T := by
        have h1 : ⁅x, b⁆ * b = x * b * x⁻¹ := by simp only [commutatorElement_def]; group
        rw [h1, mem_conjSubgroup]
        simpa [mul_assoc] using hb
      have hc0 : ⁅x, b⁆ * b ∉ normalClosureInf T (CFSG.pCore 2 K) := by
        intro h
        apply hb0
        have h2 := Subgroup.mul_mem _ (Subgroup.inv_mem _ (hcomm x hx)) h
        rwa [inv_mul_cancel_left] at h2
      have hcT := mem_of_mem_sup_normalClosureInf_of_mem_conj hT hcsup hcconj hc0
      simpa using T.mul_mem hcT (T.inv_mem hb)
    have hcent : conjSubgroup g T ≤ Subgroup.centralizer ({b} : Set K) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      by_cases hgT : conjSubgroup g T = T
      · exact elemAbelian_mul_comm hT.1 hb (hgT ▸ hx)
      · have hbot := hT.inf_conj_eq_bot hgT
        have h1 : ⁅x, b⁆ ∈ conjSubgroup g T := by
          rw [← commutatorElement_inv b x]
          exact (conjSubgroup g T).inv_mem (comm_mem_of_mem_normalizer hbN hx)
        have h3 : ⁅x, b⁆ ∈ T ⊓ conjSubgroup g T := ⟨hxT x hx, h1⟩
        rw [hbot, Subgroup.mem_bot] at h3
        exact (commutatorElement_eq_one_iff_mul_comm.1 h3).symm
    have hconj := (hT.2 b hb hb1).2 g hcent
    rw [show (↑g : K ⧸ normalClosureInf T (CFSG.pCore 2 K)) =
      QuotientGroup.mk' (normalClosureInf T (CFSG.pCore 2 K)) g from rfl, ← map_conjSubgroup,
      hconj]

theorem exists_central_quotient_map_pCore {T : Subgroup K} (hT : IsWC T)
    (hK : Subgroup.normalClosure (T : Set K) = ⊤) :
    ∃ φ : K ⧸ normalClosureInf T (CFSG.pCore 2 K) →* K ⧸ CFSG.pCore 2 K,
      (∀ k : K, φ (QuotientGroup.mk' (normalClosureInf T (CFSG.pCore 2 K)) k) =
        QuotientGroup.mk' (CFSG.pCore 2 K) k) ∧ Function.Surjective φ ∧
      φ.ker ≤ Subgroup.center (K ⧸ normalClosureInf T (CFSG.pCore 2 K)) ∧
      T.map (QuotientGroup.mk' (normalClosureInf T (CFSG.pCore 2 K))) ⊓ φ.ker = ⊥ := by
  have hN2 : IsPGroup 2 (CFSG.pCore 2 K) := CFSG.pCore_isPGroup
  have hle : normalClosureInf T (CFSG.pCore 2 K) ≤ CFSG.pCore 2 K := normalClosureInf_le T
  let φ : K ⧸ normalClosureInf T (CFSG.pCore 2 K) →* K ⧸ CFSG.pCore 2 K :=
    QuotientGroup.map _ _ (MonoidHom.id K) (by simpa using hle)
  refine ⟨φ, fun k => rfl, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨QuotientGroup.mk' (normalClosureInf T (CFSG.pCore 2 K)) k, rfl⟩
  · intro z hz
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective z
    have hkN : k ∈ CFSG.pCore 2 K := (QuotientGroup.eq_one_iff k).1 hz
    exact map_le_center_normalClosureInf hT hN2 hK (Subgroup.mem_map_of_mem _ hkN)
  · rw [eq_bot_iff]
    rintro _ ⟨⟨t, ht, rfl⟩, hz⟩
    have htN : t ∈ CFSG.pCore 2 K := (QuotientGroup.eq_one_iff t).1 hz
    exact Subgroup.mem_bot.2 ((QuotientGroup.eq_one_iff t).2
      (inf_le_normalClosureInf T _ ⟨ht, htN⟩))

theorem isWC_map_pCore {T : Subgroup K} (hT : IsWC T)
    (hK : Subgroup.normalClosure (T : Set K) = ⊤) :
    IsWC (T.map (QuotientGroup.mk' (CFSG.pCore 2 K))) := by
  obtain ⟨φ, hφ, hφsurj, hker, hbot⟩ := exists_central_quotient_map_pCore hT hK
  have hcomp : φ.comp (QuotientGroup.mk' (normalClosureInf T (CFSG.pCore 2 K))) =
      QuotientGroup.mk' (CFSG.pCore 2 K) := MonoidHom.ext hφ
  have hmain := (isWC_map_normalClosureInf hT).map_of_ker_le_center φ hφsurj hker hbot
  rwa [Subgroup.map_map, hcomp] at hmain

end Claims

end CFSG.CGT.Timmesfeld75
