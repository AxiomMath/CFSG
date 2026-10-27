module

public import CFSG.CGT.PushingUpLit.SolKNA.FinalCaseDefs
public import CFSG.RankThree.GF2n.Tim78Critical
public import CFSG.RankThree.GF2n.Tim78RootType
public import CFSG.LocalAnalysis.ComponentClassification.Asc76XLemma24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim78 CFSG.Open

variable {G : Type} [Group G]

section Restrict

variable {M V : Subgroup G}

theorem mem_conjSubgroup_subgroupOf' {B : Subgroup G} {g x : ↥M} :
    x ∈ conjSubgroup g (B.subgroupOf M) ↔ (x : G) ∈ conjSubgroup (g : G) B := by
  rw [mem_conjSubgroup, mem_conjSubgroup, Subgroup.mem_subgroupOf]
  rfl

theorem isTI_subgroupOf' (hTI : IsTI V) : IsTI (V.subgroupOf M) := by
  intro g
  rcases hTI (g : G) with h | h
  · left
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
    have : (x : G) ∈ V ⊓ conjSubgroup (g : G) V :=
      Subgroup.mem_inf.mpr ⟨hx1, mem_conjSubgroup_subgroupOf'.mp hx2⟩
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext this)
  · right
    refine le_antisymm inf_le_left fun x hx => Subgroup.mem_inf.mpr ⟨hx, ?_⟩
    rw [mem_conjSubgroup_subgroupOf']
    have hx' : (x : G) ∈ V := hx
    rw [← h] at hx'
    exact (Subgroup.mem_inf.mp hx').2

theorem isRootTypeTI_subgroupOf (hVM : V ≤ M) (hTI : IsTI V)
    (hroot : ∀ g : G, V ⊓ Subgroup.normalizer (conjSubgroup g V : Set G) ≠ ⊥ →
      ∀ a ∈ V, ∀ b ∈ conjSubgroup g V, a * b = b * a) :
    IsRootTypeTI (V.subgroupOf M) := by
  refine ⟨isTI_subgroupOf' hTI, fun g hg a ha b hb => ?_⟩
  obtain ⟨⟨t, ht⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hg
  obtain ⟨htV, htN⟩ := Subgroup.mem_inf.mp ht
  have hVg : conjSubgroup (g : G) V ≤ M := fun x hx => by
    have hx' : (g : G)⁻¹ * x * g ∈ V := mem_conjSubgroup.mp hx
    have := M.mul_mem (M.mul_mem g.2 (hVM hx')) (M.inv_mem g.2)
    rwa [show (g : G) * ((g : G)⁻¹ * x * g) * (g : G)⁻¹ = x by group] at this
  have hnorm : (t : G) ∈ Subgroup.normalizer (conjSubgroup (g : G) V : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      have h1 := (Subgroup.mem_normalizer_iff.mp htN ⟨w, hVg hw⟩).mp
        (mem_conjSubgroup_subgroupOf'.mpr hw)
      exact mem_conjSubgroup_subgroupOf'.mp h1
    · intro hw
      have hwM : (t : G) * w * (t : G)⁻¹ ∈ M := hVg hw
      have hwM' : w ∈ M := by
        have := M.mul_mem (M.mul_mem (M.inv_mem t.2) hwM) t.2
        rwa [show (t : G)⁻¹ * ((t : G) * w * (t : G)⁻¹) * t = w by group] at this
      have h1 := (Subgroup.mem_normalizer_iff.mp htN ⟨w, hwM'⟩).mpr
        (mem_conjSubgroup_subgroupOf'.mpr hw)
      exact mem_conjSubgroup_subgroupOf'.mp h1
  have hne : V ⊓ Subgroup.normalizer (conjSubgroup (g : G) V : Set G) ≠ ⊥ :=
    Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨⟨(t : G), Subgroup.mem_inf.mpr ⟨htV, hnorm⟩⟩,
      fun h' => ht1 (by
        have h1 : (t : G) = 1 := by simpa using congrArg Subtype.val h'
        have h2 : t = 1 := Subtype.ext h1
        subst h2
        rfl)⟩
  exact Subtype.ext (hroot (g : G) hne (a : G) ha (b : G) (mem_conjSubgroup_subgroupOf'.mp hb))

end Restrict

theorem exists_invol_pow {P : Subgroup G} (hP : IsPGroup 2 P) {c : G} (hc : c ∈ P) (hc1 : c ≠ 1) :
    ∃ k : ℕ, c ^ k ≠ 1 ∧ c ^ k * c ^ k = 1 := by
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hP) ⟨c, hc⟩
  have hj' : orderOf c = 2 ^ j := by rwa [Subgroup.orderOf_mk] at hj
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hj'
    exact hc1 hj'
  refine ⟨2 ^ (j - 1), fun h1 => ?_, ?_⟩
  · have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hj'] at h2
    have h3 := Nat.le_of_dvd (by positivity) h2
    have h4 : 2 ^ (j - 1) < 2 ^ j := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  · rw [← pow_add, ← two_mul, ← pow_succ']
    have : j - 1 + 1 = j := by omega
    rw [this, ← hj']
    exact pow_orderOf_eq_one c

theorem exists_pow_two_pow_eq_one {P : Subgroup G} (hP : IsPGroup 2 P) {y : G} (hy : y ∈ P) :
    ∃ k : ℕ, y ^ 2 ^ k = 1 := by
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hP) ⟨y, hy⟩
  have hj' : orderOf y = 2 ^ j := by rwa [Subgroup.orderOf_mk] at hj
  exact ⟨j, by rw [← hj']; exact pow_orderOf_eq_one y⟩

theorem mem_pCore_iff_inSubgroup (M : Subgroup G) (x : ↥M) :
    x ∈ pCore 2 ↥M ↔ (x : G) ∈ inSubgroup (pCore 2) M := by
  unfold inSubgroup
  exact ⟨fun h => ⟨x, h, rfl⟩, fun ⟨w, hw, hwz⟩ => (Subtype.ext hwz : w = x) ▸ hw⟩

abbrev qGroup (R : Subgroup G) : Subgroup G :=
  inSubgroup (pCore 2) (Subgroup.normalizer (R : Set G))

theorem comm_conj_zCenter (R : Subgroup G) (b : G) :
    ∀ x ∈ conjSubgroup b (zCenter R), ∀ y ∈ conjSubgroup b (zCenter R), x * y = y * x := by
  intro x hx y hy
  rw [conjSubgroup_zCenter] at hx hy
  exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2 y
    (Subgroup.mem_inf.mp hy).1).symm

namespace FinalCase

variable [Finite G] {R : Subgroup G} {z : G} (F : FinalCase G R z)
include F

theorem normalizer_conj_Z (b : G) :
    Subgroup.normalizer (conjSubgroup b (zCenter R) : Set G) =
      Subgroup.normalizer (conjSubgroup b R : Set G) := by
  rw [← conjSubgroup_normalizer, F.normalizer_Z, conjSubgroup_normalizer]

theorem sq_conj_Z (b : G) : ∀ x ∈ conjSubgroup b (zCenter R), x * x = 1 := by
  intro x hx
  have h1 := F.Z_sq _ (mem_conjSubgroup.mp hx)
  calc x * x = b * ((b⁻¹ * x * b) * (b⁻¹ * x * b)) * b⁻¹ := by group
    _ = 1 := by rw [h1]; group

theorem Z_comm_of_inf_ne_bot {a b : G}
    (h : conjSubgroup a (zCenter R) ⊓ Subgroup.normalizer (conjSubgroup b (zCenter R) : Set G) ≠
      ⊥) :
    ∀ x ∈ conjSubgroup a (zCenter R), ∀ y ∈ conjSubgroup b (zCenter R), x * y = y * x := by
  by_cases hab : conjSubgroup a R = conjSubgroup b R
  · have hZ : conjSubgroup a (zCenter R) = conjSubgroup b (zCenter R) := by
      rw [conjSubgroup_zCenter, conjSubgroup_zCenter, hab]
    intro x hx y hy
    rw [hZ] at hx
    exact comm_conj_zCenter R b x hx y hy
  · have h1 : conjSubgroup a R ⊓ Subgroup.normalizer (conjSubgroup b R : Set G) ≠ ⊥ := by
      intro hbot
      apply h
      rw [eq_bot_iff]
      intro w hw
      obtain ⟨hw1, hw2⟩ := Subgroup.mem_inf.mp hw
      have hw1' : w ∈ conjSubgroup a R := Subgroup.map_mono inf_le_left hw1
      have hw2' : w ∈ Subgroup.normalizer (conjSubgroup b R : Set G) := by
        rw [← F.normalizer_conj_Z b]
        exact hw2
      have : w ∈ conjSubgroup a R ⊓ Subgroup.normalizer (conjSubgroup b R : Set G) :=
        Subgroup.mem_inf.mpr ⟨hw1', hw2'⟩
      rw [hbot] at this
      exact this
    obtain ⟨-, hcomm⟩ := F.P_pair (a := b) (b := a) hab h1
    intro x hx y hy
    exact (hcomm y hy x hx).symm

theorem isRootTypeTI_conj_Z {h : G}
    (hh : conjSubgroup h (zCenter R) ≤ Subgroup.normalizer (R : Set G)) :
    IsRootTypeTI ((conjSubgroup h (zCenter R)).subgroupOf (Subgroup.normalizer (R : Set G))) := by
  refine isRootTypeTI_subgroupOf hh (isTI_conjSubgroup F.isTI_Z h) fun g hg a ha b hb => ?_
  rw [← conjSubgroup_mul] at hg hb
  exact F.Z_comm_of_inf_ne_bot (a := h) (b := g * h) hg a ha b hb


theorem le_Q_of_inf_ne_bot {h : G}
    (hh : conjSubgroup h (zCenter R) ≤ Subgroup.normalizer (R : Set G))
    (hcase : conjSubgroup h (zCenter R) ⊓ qGroup R ≠ ⊥) :
    conjSubgroup h (zCenter R) ≤ qGroup R := by
  have hV := F.isRootTypeTI_conj_Z hh
  have hVe : CFSG.Assembly.IsElemAbelian 2
      ((conjSubgroup h (zCenter R)).subgroupOf (Subgroup.normalizer (R : Set G))) :=
    ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext
      (comm_conj_zCenter R h _ a.2 _ b.2))⟩⟩, fun w hw => by
      have := F.sq_conj_Z h (w : G) hw
      apply Subtype.ext
      rw [Subgroup.coe_pow, sq]
      exact this⟩
  rcases tim78_2_13 hVe hV with h0 | hle
  · exfalso
    apply hcase
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨hw1, hw2⟩ := Subgroup.mem_inf.mp hw
    have hwM := hh hw1
    have hmem : (⟨w, hwM⟩ : ↥(Subgroup.normalizer (R : Set G))) ∈
        (conjSubgroup h (zCenter R)).subgroupOf (Subgroup.normalizer (R : Set G)) ⊓
          pCore 2 ↥(Subgroup.normalizer (R : Set G)) :=
      Subgroup.mem_inf.mpr ⟨hw1, (mem_pCore_iff_inSubgroup _ ⟨w, hwM⟩).mpr hw2⟩
    rw [h0, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hmem)
  · intro w hw
    have hwM := hh hw
    exact (mem_pCore_iff_inSubgroup _ ⟨w, hwM⟩).mp (hle hw)

theorem false_of_inf_Q_eq_bot {h : G}
    (hh : conjSubgroup h (zCenter R) ≤ Subgroup.normalizer (R : Set G))
    (hcase : conjSubgroup h (zCenter R) ⊓ qGroup R = ⊥) : False := by
  classical
  obtain ⟨hQ2, hQM, hMQ⟩ := inSubgroup_pCore_two (Subgroup.normalizer (R : Set G))
  have hR2h : IsPGroup 2 (conjSubgroup h R) := F.two.map (MulAut.conj h).toMonoidHom
  have hT2 : IsPGroup 2 ↥(conjSubgroup h R ⊓ Subgroup.normalizer (R : Set G)) :=
    hR2h.to_le inf_le_left
  have hzh : h * z * h⁻¹ ∈ conjSubgroup h (zCenter R) := by
    rw [mem_conjSubgroup, show h⁻¹ * (h * z * h⁻¹) * h = z by group]
    exact F.z_mem
  have hzh1 : h * z * h⁻¹ ≠ 1 := fun e => F.z_ne (by
    calc z = h⁻¹ * (h * z * h⁻¹) * h := by group
      _ = 1 := by rw [e]; group)
  have hzhT : h * z * h⁻¹ ∈ conjSubgroup h R ⊓ Subgroup.normalizer (R : Set G) :=
    Subgroup.mem_inf.mpr ⟨Subgroup.map_mono inf_le_left hzh, hh hzh⟩
  have hTne : conjSubgroup h R ⊓ Subgroup.normalizer (R : Set G) ≠ ⊥ := fun hb => hzh1 (by
    rw [hb, Subgroup.mem_bot] at hzhT
    exact hzhT)
  have hQT : qGroup R ⊓ (conjSubgroup h R ⊓ Subgroup.normalizer (R : Set G)) = ⊥ := by
    by_contra hne
    have hUn : (conjSubgroup h R ⊓ Subgroup.normalizer (R : Set G)) ≤ Subgroup.normalizer
        ((qGroup R ⊓ (conjSubgroup h R ⊓ Subgroup.normalizer (R : Set G)) : Subgroup G) :
          Set G) := fun t ht =>
      mem_normalizer_inf (hMQ (Subgroup.mem_inf.mp ht).2) (Subgroup.le_normalizer ht)
    obtain ⟨⟨c, hc⟩, hc1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
      (CFSG.ComponentClassification.Asc76X.inf_center_ne_bot' hT2 inf_le_right hUn hne)
    have hcT := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hc).1).2
    have hcQ := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hc).1).1
    obtain ⟨k, hk1, hk2⟩ := exists_invol_pow hT2 hcT (fun e => hc1 (Subtype.ext e))
    have hkZ := F.invol_mem h (c ^ k) (Subgroup.pow_mem _ hcT k) hk2
    have hk : c ^ k ∈ conjSubgroup h (zCenter R) ⊓ qGroup R :=
      Subgroup.mem_inf.mpr ⟨hkZ, Subgroup.pow_mem _ hcQ k⟩
    rw [hcase, Subgroup.mem_bot] at hk
    exact hk1 hk
  obtain ⟨y, hyT, hyy⟩ := F.sq_mem h hTne
  have hyR : y ∈ conjSubgroup h R := (Subgroup.mem_inf.mp hyT).1
  have hyM : y ∈ Subgroup.normalizer (R : Set G) := (Subgroup.mem_inf.mp hyT).2
  have hC : qGroup R ⊓ Subgroup.centralizer ({y} : Set G) =
      qGroup R ⊓ Subgroup.centralizer ({y ^ 2} : Set G) := by
    apply le_antisymm
    · intro q hq
      obtain ⟨hq1, hq2⟩ := Subgroup.mem_inf.mp hq
      refine Subgroup.mem_inf.mpr ⟨hq1, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hq2 ⊢
      rw [sq]
      calc q * (y * y) = (q * y) * y := by group
        _ = (y * q) * y := by rw [hq2]
        _ = y * (q * y) := by group
        _ = y * (y * q) := by rw [hq2]
        _ = (y * y) * q := by group
    · intro q hq
      obtain ⟨hq1, hq2⟩ := Subgroup.mem_inf.mp hq
      refine Subgroup.mem_inf.mpr ⟨hq1, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hq2 ⊢
      have hq3 : q * (h * z * h⁻¹) = (h * z * h⁻¹) * q := by
        rw [← hyy, ← sq]
        exact hq2
      have hqN : q ∈ Subgroup.normalizer (conjSubgroup h R : Set G) := by
        rw [← conjSubgroup_normalizer, ← F.cent_z, mem_conjSubgroup,
          Subgroup.mem_centralizer_singleton_iff]
        calc h⁻¹ * q * h * z = h⁻¹ * (q * (h * z * h⁻¹)) * h := by group
          _ = h⁻¹ * ((h * z * h⁻¹) * q) * h := by rw [hq3]
          _ = z * (h⁻¹ * q * h) := by group
      have hqT : q ∈ Subgroup.normalizer
          ((conjSubgroup h R ⊓ Subgroup.normalizer (R : Set G) : Subgroup G) : Set G) :=
        mem_normalizer_inf hqN (Subgroup.le_normalizer (hQM hq1))
      have hc : y * q * y⁻¹ * q⁻¹ ∈
          qGroup R ⊓ (conjSubgroup h R ⊓ Subgroup.normalizer (R : Set G)) := by
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · have h1 : y * q * y⁻¹ ∈ qGroup R :=
            (Subgroup.mem_normalizer_iff.mp (hMQ hyM) q).mp hq1
          exact (qGroup R).mul_mem h1 ((qGroup R).inv_mem hq1)
        · have h1 : q * y⁻¹ * q⁻¹ ∈ conjSubgroup h R ⊓ Subgroup.normalizer (R : Set G) :=
            (Subgroup.mem_normalizer_iff.mp hqT y⁻¹).mp (Subgroup.inv_mem _ hyT)
          have := Subgroup.mul_mem _ hyT h1
          rwa [show y * (q * y⁻¹ * q⁻¹) = y * q * y⁻¹ * q⁻¹ by group] at this
      rw [hQT, Subgroup.mem_bot] at hc
      calc q * y = (y * q * y⁻¹ * q⁻¹)⁻¹ * (y * q) := by group
        _ = y * q := by rw [hc, inv_one, one_mul]
  have hy2Q := tim78_2_3 F.fstar hyM (exists_pow_two_pow_eq_one hR2h hyR) hC
  have hmem : h * z * h⁻¹ ∈ conjSubgroup h (zCenter R) ⊓ qGroup R := by
    refine Subgroup.mem_inf.mpr ⟨hzh, ?_⟩
    rw [← hyy, ← sq]
    exact hy2Q
  rw [hcase, Subgroup.mem_bot] at hmem
  exact hzh1 hmem

theorem conj_Z_le_Q {h : G}
    (hh : conjSubgroup h (zCenter R) ≤ Subgroup.normalizer (R : Set G)) :
    conjSubgroup h (zCenter R) ≤ qGroup R := by
  by_cases hcase : conjSubgroup h (zCenter R) ⊓ qGroup R = ⊥
  · exact (F.false_of_inf_Q_eq_bot hh hcase).elim
  · exact F.le_Q_of_inf_ne_bot hh hcase

end FinalCase

end CFSG.CGT.PushingUpLit.SolKNA
