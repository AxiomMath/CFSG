module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk5AnConcl1
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk5AnQuot
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk5AnCore
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk5AnPermCountQbar
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk5AnTwist

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk5An

open Subgroup Equiv CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm4 CFSG.GH74.GLS.IVK.Lifted
  CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23
open scoped commutatorElement

section Arith

theorem fact_sub7_small (m : ℕ) (h7 : 7 ≤ m) (hm : m ≤ 8) : (m - 7).factorial = 1 := by
  interval_cases m <;> decide

theorem fact_sub7_big (m : ℕ) (h9 : 9 ≤ m) (h10 : m ≤ 10) :
    (m - 7).factorial = if m = 10 then 6 else 2 := by
  interval_cases m <;> decide

theorem sw89_mem (m : ℕ) (h7 : 7 ≤ m) (h10 : m ≤ 10) (h9 : 9 ≤ m) :
    sw m 8 9 ∈ Subgroup.centralizer ({ub m, vb m, xb1 m, xb2 m, tb m} : Set (Perm (Fin (m + 1)))) := by
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl <;> interval_cases m <;> decide

theorem sign_sw89 (m : ℕ) (h7 : 7 ≤ m) (h10 : m ≤ 10) (h9 : 9 ≤ m) : Perm.sign (sw m 8 9) = -1 := by
  have hne : Fin.ofNat (m + 1) 8 ≠ Fin.ofNat (m + 1) 9 := by interval_cases m <;> decide
  exact Perm.sign_swap hne

theorem mem_normalizer_of_conj {G : Type*} [Group G] {S : Subgroup G} {g : G}
    (h1 : ∀ s ∈ S, g * s * g⁻¹ ∈ S) (h2 : ∀ s ∈ S, g⁻¹ * s * g ∈ S) :
    g ∈ normalizer (S : Set G) := by
  rw [mem_normalizer_iff]
  intro s
  refine ⟨fun hs => h1 s hs, fun hs => ?_⟩
  have h3 := h2 _ hs
  have e : g⁻¹ * (g * s * g⁻¹) * g = s := by group
  rwa [e] at h3

end Arith

section Basic

variable {H : Type} [Group H] {K : Subgroup H} {m : ℕ}

theorem card_ZK {n : ℕ} [Finite H] (hH : Hyp5B H K n) : Nat.card ↥(ZK K) = 2 := by
  have h1 : Nat.card ↥(ZK K) = Nat.card ↥(center ↥K) :=
    Subgroup.card_map_of_injective K.subtype_injective
  rw [h1]
  exact hH.cover.2.1

namespace Cfg

variable {R : PermRep K (m + 1)} {z : H} (Γ : Cfg R z)

include Γ

theorem ZQ_le_Q : Γ.ZQ ≤ Γ.Q := Subgroup.map_subtype_le _

theorem ZQ_le_J : Γ.ZQ ≤ Γ.J := le_trans Γ.ZQ_le_Q Γ.Q_le_J

theorem c_mem_C : Γ.L.c ∈ Γ.C := Γ.X_le_C (mem_zpowers _)

theorem J_le_normalizer_Q : Γ.J ≤ normalizer (Γ.Q : Set H) := fun j hj =>
  mem_normalizer_of_conj (fun s hs => Γ.J_norm_Q j hj s hs) (fun s hs => by
    simpa using Γ.J_norm_Q j⁻¹ (inv_mem hj) s hs)

theorem eq_of_rho_mem {y : H} (h : R.ρ y = 1 ∨ R.ρ y = tb m) :
    y = 1 ∨ y = z ∨ y = Γ.t ∨ y = Γ.t * z := by
  rcases h with h | h
  · rcases Γ.hz.ker y h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
  · have h5 : R.ρ (Γ.t⁻¹ * y) = 1 := by
      rw [map_mul, map_inv, Γ.rho_t', h, inv_mul_cancel]
    rcases Γ.hz.ker _ h5 with h' | h'
    · right; right; left
      calc y = Γ.t * (Γ.t⁻¹ * y) := by group
        _ = Γ.t := by rw [h', mul_one]
    · right; right; right
      calc y = Γ.t * (Γ.t⁻¹ * y) := by group
        _ = Γ.t * z := by rw [h']

theorem Q_cent_X {q : H} (hq : q ∈ Γ.Q) (hc : q * Γ.L.c = Γ.L.c * q) :
    q = 1 ∨ q = z ∨ q = Γ.t ∨ q = Γ.t * z := by
  obtain ⟨x, hx⟩ := Γ.rho_of_mem_Q hq
  have h1 := congrArg R.ρ hc
  rw [map_mul, map_mul, hx, Γ.L.hc] at h1
  exact Γ.eq_of_rho_mem (by
    rw [hx]
    exact Sfun_cent_c3 m Γ.h7 Γ.h10 x h1.symm)

theorem t_mem_cent_X : Γ.t ∈ centralizer (Γ.X : Set H) := by
  rw [mem_centralizer_iff]
  intro x hx
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
  exact (Commute.zpow_left Γ.c_comm_t k).eq

theorem z_mem_cent_X : z ∈ centralizer (Γ.X : Set H) := by
  rw [mem_centralizer_iff]
  intro x _
  exact Γ.hz.central x

theorem ZQ_le_cent_X : Γ.ZQ ≤ centralizer (Γ.X : Set H) := by
  rw [Γ.center_Q]
  refine sup_le ?_ ?_
  · rw [zpowers_le]; exact Γ.t_mem_cent_X
  · rw [zpowers_le]; exact Γ.z_mem_cent_X

theorem Q_inf_cent_X : Γ.Q ⊓ centralizer (Γ.X : Set H) = Γ.ZQ := by
  apply le_antisymm
  · intro q hq
    obtain ⟨hqQ, hqc⟩ := Subgroup.mem_inf.mp hq
    have hc : q * Γ.L.c = Γ.L.c * q :=
      (mem_centralizer_iff.mp hqc Γ.L.c (mem_zpowers _)).symm
    rw [Γ.center_Q]
    rcases Γ.Q_cent_X hqQ hc with h | h | h | h <;> rw [h]
    · exact one_mem _
    · exact Subgroup.mem_sup_right (mem_zpowers z)
    · exact Subgroup.mem_sup_left (mem_zpowers _)
    · exact mul_mem (Subgroup.mem_sup_left (mem_zpowers _)) (Subgroup.mem_sup_right (mem_zpowers z))
  · exact le_inf Γ.ZQ_le_Q Γ.ZQ_le_cent_X

theorem CenK_ZQ : CenK K (Γ.ZQ : Set H) = Γ.C := by
  ext y
  unfold CenK C
  simp only [Subgroup.mem_inf]
  constructor
  · rintro ⟨hyK, hy⟩
    refine ⟨hyK, ?_⟩
    rw [mem_centralizer_iff] at hy ⊢
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    have ht : Γ.t ∈ (Γ.ZQ : Set H) := by
      rw [SetLike.mem_coe, Γ.center_Q]
      exact Subgroup.mem_sup_left (mem_zpowers _)
    exact hy Γ.t ht
  · rintro ⟨hyK, hy⟩
    refine ⟨hyK, ?_⟩
    have hty : Γ.t * y = y * Γ.t := (mem_centralizer_singleton_iff.mp hy).symm
    have hle : Γ.ZQ ≤ centralizer ({y} : Set H) := by
      rw [Γ.center_Q]
      refine sup_le ?_ ?_
      · rw [zpowers_le, mem_centralizer_singleton_iff]; exact hty
      · rw [zpowers_le, mem_centralizer_singleton_iff]; exact (Γ.hz.central y).symm
    rw [mem_centralizer_iff]
    intro h hh
    exact mem_centralizer_singleton_iff.mp (hle hh)

theorem card_cent_Q_le [Finite H] : Nat.card ↥(CenK K (Γ.Q : Set H)) ≤ if m = 10 then 12 else 4 := by
  set G : Subgroup H := CenK K (Γ.Q : Set H) with hG
  let f : ↥G →* Perm (Fin (m + 1)) := R.ρ.comp G.subtype
  have hGcent : ∀ g : ↥G, ∀ u ∈ Γ.Q, u * (g : H) = (g : H) * u := fun g u hu =>
    mem_centralizer_iff.mp (Subgroup.mem_inf.mp g.2).2 u hu
  have hcom : ∀ (g : ↥G), ∀ u ∈ Γ.Q, R.ρ (g : H) * R.ρ u = R.ρ u * R.ρ (g : H) := by
    intro g u hu
    rw [← map_mul, ← map_mul, hGcent g u hu]
  have hcomm : ∀ g ∈ f.range, ∀ q ∈ ({ub m, vb m, xb1 m, xb2 m, tb m} :
      Set (Perm (Fin (m + 1)))), g * q = q * g := by
    rintro _ ⟨d, rfl⟩ q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · have := hcom d Γ.L.u Γ.u_mem_Q
      rwa [Γ.L.hu] at this
    · have := hcom d Γ.L.v Γ.v_mem_Q
      rwa [Γ.L.hv] at this
    · have := hcom d Γ.L.x1 Γ.x1_mem_Q
      rwa [Γ.L.hx1] at this
    · have := hcom d Γ.L.x2 Γ.x2_mem_Q
      rwa [Γ.L.hx2] at this
    · have := hcom d Γ.t Γ.t_mem_Q
      rwa [Γ.rho_t'] at this
  have hker : Nat.card ↥f.ker ≤ 2 := by
    have hord : Nat.card ↥(zpowers z) = 2 := by rw [Nat.card_zpowers]; exact Γ.orderOf_z
    rw [← hord]
    refine Nat.card_le_card_of_injective
      (fun x : ↥f.ker => (⟨(((x : ↥G)) : H), ?_⟩ : ↥(zpowers z))) ?_
    · have hx : R.ρ (((x : ↥G)) : H) = 1 := x.2
      rcases Γ.hz.ker _ hx with h | h
      · rw [h]; exact one_mem _
      · rw [h]; exact mem_zpowers z
    · intro x y hxy
      exact Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hxy))
  have hGcard : Nat.card ↥G = Nat.card ↥f.ker * Nat.card ↥f.range :=
    (Subgroup.card_ker_mul_card_range f).symm
  set P0 : Subgroup (Perm (Fin (m + 1))) :=
    Subgroup.centralizer ({ub m, vb m, xb1 m, xb2 m, tb m} : Set (Perm (Fin (m + 1)))) with hP0
  have hf_le : f.range ≤ P0 := by
    rintro g hg
    rw [hP0, mem_centralizer_iff]
    intro h hh
    exact (hcomm g hg h hh).symm
  have hf_alt : f.range ≤ P0 ⊓ alternatingGroup (Fin (m + 1)) := by
    intro g hg
    refine Subgroup.mem_inf.mpr ⟨hf_le hg, ?_⟩
    obtain ⟨d, rfl⟩ := hg
    rw [Perm.mem_alternatingGroup]
    exact R.sign_of_mem_K _ (Subgroup.mem_inf.mp d.2).1
  have hdvd : Nat.card ↥P0 ∣ (m - 7).factorial * 2 :=
    card_dvd_cent_Qbar m Γ.h7 Γ.h10 P0 (fun g hg q hq => by
      rw [hP0, mem_centralizer_iff] at hg
      exact (hg q hq).symm)
  have hP0le : Nat.card ↥P0 ≤ (m - 7).factorial * 2 := Nat.le_of_dvd (by positivity) hdvd
  by_cases h9 : 9 ≤ m
  · have hodd := card_eq_two_mul_card_inf_alt P0 (sw89_mem m Γ.h7 Γ.h10 h9)
      (sign_sw89 m Γ.h7 Γ.h10 h9)
    have hrange : Nat.card ↥f.range ≤ Nat.card ↥(P0 ⊓ alternatingGroup (Fin (m + 1))) :=
      Subgroup.card_le_of_le hf_alt
    have hfact := fact_sub7_big m h9 Γ.h10
    rw [hGcard]
    split_ifs at hfact ⊢ with h10'
    · have h6 : Nat.card ↥f.range ≤ 6 := by omega
      calc Nat.card ↥f.ker * Nat.card ↥f.range ≤ 2 * 6 := Nat.mul_le_mul hker h6
        _ = 12 := by norm_num
    · have h2 : Nat.card ↥f.range ≤ 2 := by omega
      calc Nat.card ↥f.ker * Nat.card ↥f.range ≤ 2 * 2 := Nat.mul_le_mul hker h2
        _ = 4 := by norm_num
  · have hfact := fact_sub7_small m Γ.h7 (by omega)
    have hrange : Nat.card ↥f.range ≤ Nat.card ↥P0 := Subgroup.card_le_of_le hf_le
    rw [hGcard]
    split_ifs with h10'
    · omega
    · have h2 : Nat.card ↥f.range ≤ 2 := by omega
      calc Nat.card ↥f.ker * Nat.card ↥f.range ≤ 2 * 2 := Nat.mul_le_mul hker h2
        _ = 4 := by norm_num

theorem concl53f_small [Finite H] (hm : m ≤ 8) : QuotIso Γ.C Γ.Q (alternatingGroup (Fin 3)) := by
  have hCJ : Γ.C = Γ.J := by
    have hcard : Nat.card ↥Γ.C ≤ Nat.card ↥Γ.J := by
      rw [Γ.J_card]
      have h1 := Γ.C_card_le
      rw [fact_sub7_small m Γ.h7 hm] at h1
      omega
    exact (Subgroup.eq_of_le_of_card_ge Γ.J_le_C hcard).symm
  have hQC : Γ.Q ≤ Γ.C := Γ.Q_le_C
  have hnorm : Γ.C ≤ normalizer (Γ.Q : Set H) := by rw [hCJ]; exact Γ.J_le_normalizer_Q
  have : (Γ.Q.subgroupOf Γ.C).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hnorm
  have hN : Nat.card ↥(Γ.Q.subgroupOf Γ.C) = 64 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQC).toEquiv]
    exact Γ.Q_card
  have hCcard : Nat.card ↥Γ.C = 192 := by rw [hCJ]; exact Γ.J_card
  have hidx : (Γ.Q.subgroupOf Γ.C).index = 3 := by
    have h1 := Subgroup.index_mul_card (Γ.Q.subgroupOf Γ.C)
    rw [hN, hCcard] at h1
    omega
  have hcard : Nat.card (↥Γ.C ⧸ Γ.Q.subgroupOf Γ.C) = 3 := by
    rw [← Subgroup.index_eq_card]
    exact hidx
  exact exists_hom_alternating_three (Γ.Q.subgroupOf Γ.C) hcard

end Cfg

namespace Cfg.Decomp

variable {R : PermRep K (m + 1)} {z : H} {Γ : Cfg R z} (d : Decomp Γ)

include d

theorem cent_K_Q [Finite H] : CenK K (Γ.Q : Set H) = Γ.ZQ ⊔ d.O := by
  have hle : Γ.ZQ ⊔ d.O ≤ CenK K (Γ.Q : Set H) := by
    refine sup_le ?_ ?_
    · refine le_inf (le_trans Γ.ZQ_le_Q Γ.Q_le_K) ?_
      intro y hy
      rw [mem_centralizer_iff]
      intro h hh
      obtain ⟨c, hc, rfl⟩ := hy
      exact congrArg Subtype.val (mem_center_iff.mp hc ⟨h, hh⟩)
    · refine le_inf (le_trans d.O_le_C inf_le_left) ?_
      intro o ho
      rw [mem_centralizer_iff]
      intro h hh
      exact d.O_comm h (Γ.Q_le_J hh) o ho
  have hcomm : ∀ x ∈ Γ.ZQ, ∀ y ∈ d.O, x * y = y * x := fun x hx y hy =>
    d.O_comm x (Γ.ZQ_le_J hx) y hy
  have hdisj : Γ.ZQ ⊓ d.O = ⊥ := by
    rw [eq_bot_iff, ← d.O_disj]
    exact inf_le_inf_right _ Γ.ZQ_le_J
  have hcard : Nat.card ↥(Γ.ZQ ⊔ d.O) = 4 * Nat.card ↥d.O := by
    have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute Γ.ZQ d.O hcomm).1
    rw [hdisj, Subgroup.card_bot, mul_one, Γ.card_center_Q] at h
    exact h
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  have h1 := Γ.card_cent_Q_le
  rw [hcard, d.O_card]
  split_ifs at h1 ⊢ <;> omega

theorem C_le_normalizer_Q (h9 : 9 ≤ m) : Γ.C ≤ normalizer (Γ.Q : Set H) := by
  rw [d.C_eq]
  refine sup_le (sup_le Γ.J_le_normalizer_Q ?_) ?_
  · intro o ho
    refine mem_normalizer_of_conj (fun s hs => ?_) (fun s hs => ?_)
    · have h1 : s * o = o * s := d.O_comm s (Γ.Q_le_J hs) o ho
      have h2 : o * s * o⁻¹ = s := by rw [← h1]; group
      rw [h2]; exact hs
    · have h1 : s * o = o * s := d.O_comm s (Γ.Q_le_J hs) o ho
      have h2 : o⁻¹ * s * o = s := by
        calc o⁻¹ * s * o = o⁻¹ * (s * o) := by group
          _ = o⁻¹ * (o * s) := by rw [h1]
          _ = s := by group
      rw [h2]; exact hs
  · rw [zpowers_le]
    have hvinv : d.v⁻¹ = d.v := inv_eq_of_mul_eq_one_right d.v_sq
    refine mem_normalizer_of_conj (fun s hs => Γ.v_conj_Q (d.v_rho h9) h9 hs) (fun s hs => ?_)
    rw [hvinv]
    have := Γ.v_conj_Q (d.v_rho h9) h9 hs
    rwa [hvinv] at this

theorem concl53e : Concl53e K (m + 1) Γ.ZQ := by
  unfold Concl53e
  rw [CenK_ZQ, d.pPrimeCoreOf_eq, d.O_card]
  split_ifs <;> first | rfl | omega

theorem concl53c : Concl53c K Γ.ZQ := by
  unfold Concl53c
  rw [CenK_ZQ, d.O2core_eq]
  exact ⟨Γ.QEquiv.symm.trans sylLCongr.symm⟩

theorem concl53d [Finite H] : Concl53d K Γ.ZQ := by
  unfold Concl53d
  rw [CenK_ZQ, d.O2core_eq, d.pPrimeCoreOf_eq]
  refine ⟨d.cent_K_Q, ?_, fun u hu o ho => d.O_comm u (Γ.ZQ_le_J hu) o ho⟩
  rw [eq_bot_iff, ← d.O_disj]
  exact inf_le_inf_right _ Γ.ZQ_le_J

theorem concl53ab [Finite H] : Concl53ab K Γ.ZQ := by
  unfold Concl53ab
  rw [CenK_ZQ, d.O2core_eq, d.pPrimeCoreOf_eq]
  have hQ2 : IsPGroup 2 ↥Γ.Q := IsPGroup.of_card (n := 6) (by rw [Γ.Q_card]; norm_num)
  have hQM : Γ.Q ≤ O2res Γ.C := Γ.Q_le_O2res
  refine ⟨Γ.X, Γ.X_le_C, Γ.X_card, ⟨d.v, d.v_le_C, ?_, ?_⟩, Γ.comm_QX, ?_, Γ.Q_inf_cent_X⟩
  · rw [pow_two]; exact d.v_sq
  · intro c hc
    obtain ⟨m', hm', w, hw, rfl⟩ := d.mem_C.mp hc
    obtain ⟨j, hj, o, ho, rfl⟩ := d.mem_M.mp hm'
    obtain ⟨q, hq, x, hx, rfl⟩ := Γ.mem_J_iff.mp hj
    refine ⟨o, ho, q, hq, x, hx, w, hw, ?_⟩
    have h := d.O_comm (q * x) hj o ho
    calc q * x * o * w = (o * (q * x)) * w := by rw [h]
      _ = o * q * x * w := by group
  ·
    have hP : IsPGroup 2 ↥(Γ.Q.subgroupOf (O2res Γ.C)) :=
      IsPGroup.of_equiv hQ2 (Subgroup.subgroupOfEquivOfLe hQM).symm
    have hMcard : Nat.card ↥(O2res Γ.C) = 192 * Nat.card ↥d.O := by
      have hcomm := d.O_comm
      have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute Γ.J d.O hcomm).1
      rw [d.O_disj, Subgroup.card_bot, mul_one, Γ.J_card] at h
      rw [d.O2res_eq]
      exact h
    have hNcard : Nat.card ↥(Γ.Q.subgroupOf (O2res Γ.C)) = 64 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQM).toEquiv]
      exact Γ.Q_card
    have hidx : ¬ 2 ∣ (Γ.Q.subgroupOf (O2res Γ.C)).index := by
      have h1 := Subgroup.index_mul_card (Γ.Q.subgroupOf (O2res Γ.C))
      rw [hNcard, hMcard, d.O_card] at h1
      split_ifs at h1 <;> omega
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine ⟨hP.toSylow hidx, ?_⟩
    show Subgroup.map (O2res Γ.C).subtype ((hP.toSylow hidx : Sylow 2 ↥(O2res Γ.C)) : Subgroup _) = Γ.Q
    rw [IsPGroup.toSylow_coe, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQM]

theorem concl53f_large (h9 : 9 ≤ m) : QuotIso Γ.C (d.O ⊔ Γ.Q) (Equiv.Perm (Fin 3)) := by
  have hCle : Γ.C ≤ normalizer ((d.O ⊔ Γ.Q : Subgroup H) : Set H) :=
    le_trans (le_inf d.C_le_normalizer_O (d.C_le_normalizer_Q h9))
      (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have : ((d.O ⊔ Γ.Q).subgroupOf Γ.C).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hCle
  have hvρ := d.v_rho h9
  have hOQ : ∀ o ∈ d.O, ∀ q ∈ Γ.Q, o * q = q * o := fun o ho q hq =>
    (d.O_comm q (Γ.Q_le_J hq) o ho).symm
  have hsup : ∀ y, y ∈ d.O ⊔ Γ.Q ↔ ∃ o ∈ d.O, ∃ q ∈ Γ.Q, y = o * q := fun y =>
    mem_sup_iff_mul_of_commute hOQ
  refine exists_hom_perm_three ((d.O ⊔ Γ.Q).subgroupOf Γ.C) ⟨Γ.L.c, Γ.c_mem_C⟩ ⟨d.v, d.v_le_C⟩
    ?_ ?_ ?_ ?_ ?_ ?_
  · rw [Subgroup.mem_subgroupOf]
    show Γ.L.c ^ 3 ∈ d.O ⊔ Γ.Q
    rw [Γ.L.hc3]; exact one_mem _
  · rw [Subgroup.mem_subgroupOf]
    intro hc
    have hc' : Γ.L.c ∈ d.O ⊔ Γ.Q := hc
    obtain ⟨o, ho, q, hq, hcoq⟩ := (hsup _).mp hc'
    have hoJ : o ∈ Γ.J := by
      have : o = Γ.L.c * q⁻¹ := by rw [hcoq]; group
      rw [this]
      exact mul_mem (Γ.X_le_J (mem_zpowers _)) (inv_mem (Γ.Q_le_J hq))
    have ho1 : o = 1 := by
      have : o ∈ Γ.J ⊓ d.O := ⟨hoJ, ho⟩
      rw [d.O_disj, mem_bot] at this
      exact this
    have hcq : Γ.L.c ∈ Γ.Q := by
      rw [hcoq, ho1, one_mul]; exact hq
    have hc1 : Γ.L.c ∈ Γ.Q ⊓ Γ.X := ⟨hcq, mem_zpowers _⟩
    rw [Γ.Q_disj_X.eq_bot, mem_bot] at hc1
    exact Γ.c_ne_one hc1
  · rw [Subgroup.mem_subgroupOf]
    show d.v ^ 2 ∈ d.O ⊔ Γ.Q
    rw [pow_two, d.v_sq]; exact one_mem _
  · rw [Subgroup.mem_subgroupOf]
    intro hv
    have : d.v ∈ Γ.J ⊔ d.O :=
      (sup_le (le_sup_right : d.O ≤ Γ.J ⊔ d.O) (le_trans Γ.Q_le_J le_sup_left)) hv
    exact d.v_not_mem h9 this
  · rw [Subgroup.mem_subgroupOf]
    show d.v * Γ.L.c * d.v⁻¹ * Γ.L.c ∈ d.O ⊔ Γ.Q
    have h1 : R.ρ (d.v * Γ.L.c * d.v⁻¹) = R.ρ Γ.L.c⁻¹ := by
      rw [map_mul, map_mul, map_inv, map_inv, hvρ, Γ.L.hc]
      exact vp_c3 m Γ.h7 Γ.h10 h9
    rcases conj_mem_ker Γ.hz h1 with h | h
    · rw [h]
      have : Γ.L.c⁻¹ * Γ.L.c = 1 := inv_mul_cancel _
      rw [this]; exact one_mem _
    · rw [h]
      have : Γ.L.c⁻¹ * z * Γ.L.c = z := by
        calc Γ.L.c⁻¹ * z * Γ.L.c = (z * Γ.L.c⁻¹) * Γ.L.c := by rw [Γ.hz.central Γ.L.c⁻¹]
          _ = z := by group
      rw [this]
      exact Subgroup.mem_sup_right Γ.z_mem_Q
  · intro g
    obtain ⟨m', hm', w, hw, hgw⟩ := d.mem_C.mp g.2
    obtain ⟨j, hj, o, ho, hjo⟩ := d.mem_M.mp hm'
    obtain ⟨q, hq, x, hx, hqx⟩ := Γ.mem_J_iff.mp hj
    obtain ⟨i, hi⟩ : ∃ i : ℕ, x = Γ.L.c ^ i := by
      rcases mem_zpowers_cube Γ.L.hc3 hx with h | h | h
      · exact ⟨0, by rw [h, pow_zero]⟩
      · exact ⟨1, by rw [h, pow_one]⟩
      · exact ⟨2, by rw [h, pow_two]⟩
    obtain ⟨jj, hjj⟩ : ∃ jj : ℕ, w = d.v ^ jj := by
      rcases mem_zpowers_involution d.v_sq hw with h | h
      · exact ⟨0, by rw [h, pow_zero]⟩
      · exact ⟨1, by rw [h, pow_one]⟩
    have hC : q * o ∈ Γ.C := mul_mem (Γ.Q_le_C hq) (d.O_le_C ho)
    have hN : (⟨q * o, hC⟩ : ↥Γ.C) ∈ (d.O ⊔ Γ.Q).subgroupOf Γ.C := by
      rw [Subgroup.mem_subgroupOf]
      exact mul_mem (Subgroup.mem_sup_right hq) (Subgroup.mem_sup_left ho)
    refine ⟨⟨q * o, hC⟩, hN, i, jj, ?_⟩
    apply Subtype.ext
    have hxo : x * o = o * x := d.O_comm x (Γ.X_le_J hx) o ho
    rw [hi] at hxo
    show (g : H) = q * o * Γ.L.c ^ i * d.v ^ jj
    rw [hgw, hjo, hqx, hi, hjj]
    calc q * Γ.L.c ^ i * o * d.v ^ jj = q * (Γ.L.c ^ i * o) * d.v ^ jj := by group
      _ = q * (o * Γ.L.c ^ i) * d.v ^ jj := by rw [hxo]
      _ = q * o * Γ.L.c ^ i * d.v ^ jj := by group

theorem concl53f [Finite H] : Concl53f K (m + 1) Γ.ZQ := by
  unfold Concl53f
  rw [CenK_ZQ, d.O2core_eq, d.pPrimeCoreOf_eq]
  exact ⟨fun hn => Γ.concl53f_small (by omega), fun hn => d.concl53f_large (by omega)⟩

end Cfg.Decomp

end Basic

theorem ivk_5_3 : IVK_5_3 := by
  intro H _ _ K n hH U hUK hU4 hZU
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hH.n_ge; omega⟩
  have hZKcard := card_ZK hH
  obtain ⟨t, htU, htZ⟩ : ∃ t ∈ U, t ∉ ZK K := by
    by_contra hcon
    push Not at hcon
    have hle : U ≤ ZK K := hcon
    have h := Subgroup.card_le_of_le hle
    rw [hU4.2, hZKcard] at h
    omega
  have htK : t ∈ K := hUK htU
  have ht1 : t ≠ 1 := fun h => htZ (h ▸ one_mem _)
  have ht2 : orderOf t = 2 := by
    have h1 : orderOf (⟨t, htU⟩ : ↥U) ∣ 2 :=
      (Monoid.order_dvd_exponent _).trans hU4.1.exponent_dvd_p
    rw [← Subgroup.orderOf_coe] at h1
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) ht1
    · exact h
  obtain ⟨R, z, Γ, hΓ⟩ := exists_cfg hH htK ht2 htZ
  obtain ⟨d⟩ := Γ.decomp
  have hZ : ZK K = zpowers z := ZK_eq_zpowers hH Γ.hz (z_mem_ZK Γ.hz)
  have hzU : z ∈ U := hZU (hZ ▸ mem_zpowers z)
  have hZQU : Γ.ZQ ≤ U := by
    rw [Γ.center_Q]
    refine sup_le ?_ ?_
    · rw [zpowers_le, hΓ]; exact htU
    · rw [zpowers_le]; exact hzU
  have hUZQ : Γ.ZQ = U :=
    Subgroup.eq_of_le_of_card_ge hZQU (by rw [hU4.2, Γ.card_center_Q])
  subst hUZQ
  exact ⟨d.concl53ab, d.concl53c, d.concl53d, d.concl53e, d.concl53f⟩

end CFSG.GH74.GLS.IVK.Proofs2.Ivk5An
