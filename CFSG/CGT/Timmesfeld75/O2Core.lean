module

public import CFSG.CGT.Timmesfeld75.Config
public import CFSG.ThirdParty.QiuzhenCFSG.BaerSuzuki.FinalTheorem

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

variable {K : Type*} [Group K]

section Normalizing

theorem mem_normalizer_of_commutator_mem [Finite K] {T N : Subgroup K} (hT : IsWC T) [N.Normal]
    (hN : IsPGroup 2 N) {b : K} (hb : ∀ x ∈ T, ⁅b, x⁆ ∈ N) :
    b ∈ Subgroup.normalizer (T : Set K) := by
  have hS : IsPGroup 2 (T ⊔ N : Subgroup K) :=
    (isPGroup_two_of_isElemAbelian hT.1).to_sup_of_normal_right hN
  have hle : conjSubgroup b T ≤ T ⊔ N := by
    intro y hy
    have hx : b⁻¹ * y * b ∈ T := mem_conjSubgroup.1 hy
    have hy' : y = ⁅b, b⁻¹ * y * b⁆ * (b⁻¹ * y * b) := by
      simp only [commutatorElement_def]; group
    rw [hy']
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (hb _ hx)) (Subgroup.mem_sup_left hx)
  exact mem_normalizer_of_conjSubgroup_eq (eq_of_conj_le_pGroup hT hS le_sup_left hle)

theorem le_normalizer_of_normal_pGroup [Finite K] {T N : Subgroup K} (hT : IsWC T)
    [hNn : N.Normal] (hN : IsPGroup 2 N) : N ≤ Subgroup.normalizer (T : Set K) := by
  intro u hu
  refine mem_normalizer_of_commutator_mem hT hN fun x _ => ?_
  have h : ⁅u, x⁆ = u * (x * u⁻¹ * x⁻¹) := by simp only [commutatorElement_def, mul_assoc]
  rw [h]
  exact N.mul_mem hu (hNn.conj_mem u⁻¹ (N.inv_mem hu) x)

end Normalizing

section NormalClosureInf

@[expose] def normalClosureInf (T N : Subgroup K) : Subgroup K :=
  Subgroup.normalClosure ((T ⊓ N : Subgroup K) : Set K)

instance normalClosureInf_normal (T N : Subgroup K) : (normalClosureInf T N).Normal :=
  Subgroup.normalClosure_normal

theorem inf_le_normalClosureInf (T N : Subgroup K) : T ⊓ N ≤ normalClosureInf T N :=
  Subgroup.le_normalClosure

theorem normalClosureInf_le (T : Subgroup K) {N : Subgroup K} [N.Normal] :
    normalClosureInf T N ≤ N :=
  Subgroup.normalClosure_le_normal fun _ hx => hx.2

theorem normalClosureInf_eq_bot_of_inf_eq_bot {T N : Subgroup K} (h : T ⊓ N = ⊥) :
    normalClosureInf T N = ⊥ := by
  refine le_bot_iff.1 (Subgroup.normalClosure_le_normal (N := ⊥) fun x hx => ?_)
  have hx' : x ∈ T ⊓ N := hx
  rw [h] at hx'
  exact hx'

theorem conjSubgroup_inf_le_normalClosureInf (T : Subgroup K) {N : Subgroup K} [hN : N.Normal]
    (c : K) : conjSubgroup c T ⊓ N ≤ normalClosureInf T N := by
  rintro y ⟨hyT, hyN⟩
  have h1 : c⁻¹ * y * c ∈ T ⊓ N :=
    ⟨mem_conjSubgroup.1 hyT, by simpa using hN.conj_mem y hyN c⁻¹⟩
  have h2 := (normalClosureInf_normal T N).conj_mem _ (inf_le_normalClosureInf T N h1) c
  simpa [mul_assoc] using h2

theorem isElemAbelian_closure_two {X : Set K} (hsq : ∀ x ∈ X, x ^ 2 = 1)
    (hcomm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) : IsElemAbelian 2 (Subgroup.closure X) := by
  have hcX : ∀ x ∈ X, ∀ z ∈ Subgroup.closure X, x * z = z * x := by
    intro x hx z hz
    have hle : Subgroup.closure X ≤ Subgroup.centralizer ({x} : Set K) := by
      rw [Subgroup.closure_le]
      intro y hy
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact hcomm x hx y hy
    exact Subgroup.mem_centralizer_iff.1 (hle hz) x (Set.mem_singleton x)
  have hcc : ∀ z ∈ Subgroup.closure X, ∀ w ∈ Subgroup.closure X, z * w = w * z := by
    intro z hz w hw
    have hle : Subgroup.closure X ≤ Subgroup.centralizer ({z} : Set K) := by
      rw [Subgroup.closure_le]
      intro y hy
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact (hcX y hy z hz).symm
    exact Subgroup.mem_centralizer_iff.1 (hle hw) z (Set.mem_singleton z)
  refine ⟨⟨⟨fun a b => Subtype.ext (hcc a a.2 b b.2)⟩⟩, fun z hz => ?_⟩
  refine Subgroup.closure_induction (p := fun z _ => z ^ 2 = 1) (fun x hx => hsq x hx)
    (by simp) ?_ ?_ hz
  · intro x y hx hy hx2 hy2
    rw [(show Commute x y from hcc x hx y hy).mul_pow, hx2, hy2, one_mul]
  · intro x _ hx
    rw [inv_pow, hx, inv_one]

theorem mul_comm_of_mem_inf_conj [Finite K] {T N : Subgroup K} (hT : IsWC T) [N.Normal]
    (hN : IsPGroup 2 N) {c c' y y' : K} (hy : y ∈ conjSubgroup c T) (hyN : y ∈ N)
    (hy' : y' ∈ conjSubgroup c' T) (hy'N : y' ∈ N) : y * y' = y' * y := by
  by_cases hcc : conjSubgroup c T = conjSubgroup c' T
  · exact elemAbelian_mul_comm (isElemAbelian_conjSubgroup hT.1 c) hy (hcc ▸ hy')
  · have hbot : conjSubgroup c T ⊓ conjSubgroup c' T = ⊥ := by
      have hne : conjSubgroup (c' * c⁻¹) (conjSubgroup c T) ≠ conjSubgroup c T := by
        rw [conjSubgroup_conjSubgroup, mul_assoc, inv_mul_cancel, mul_one]
        exact fun h => hcc h.symm
      have := (hT.conj c).inf_conj_eq_bot hne
      rwa [conjSubgroup_conjSubgroup, mul_assoc, inv_mul_cancel, mul_one] at this
    have h1 : ⁅y', y⁆ ∈ conjSubgroup c T :=
      comm_mem_of_mem_normalizer (le_normalizer_of_normal_pGroup (hT.conj c) hN hy'N) hy
    have h2 : ⁅y, y'⁆ ∈ conjSubgroup c' T :=
      comm_mem_of_mem_normalizer (le_normalizer_of_normal_pGroup (hT.conj c') hN hyN) hy'
    have h1' : ⁅y, y'⁆ ∈ conjSubgroup c T := by
      rw [← commutatorElement_inv y' y]
      exact Subgroup.inv_mem _ h1
    have h3 : ⁅y, y'⁆ ∈ conjSubgroup c T ⊓ conjSubgroup c' T := ⟨h1', h2⟩
    rw [hbot, Subgroup.mem_bot] at h3
    exact commutatorElement_eq_one_iff_mul_comm.1 h3

theorem isElemAbelian_normalClosureInf [Finite K] {T N : Subgroup K} (hT : IsWC T) [hN : N.Normal]
    (hN2 : IsPGroup 2 N) : IsElemAbelian 2 (normalClosureInf T N) := by
  have hgen : ∀ y ∈ Group.conjugatesOfSet ((T ⊓ N : Subgroup K) : Set K),
      ∃ c : K, y ∈ conjSubgroup c T ∧ y ∈ N ∧ y ^ 2 = 1 := by
    intro y hy
    obtain ⟨a, ha, hconj⟩ := Group.mem_conjugatesOfSet_iff.1 hy
    obtain ⟨c, rfl⟩ := isConj_iff.1 hconj
    refine ⟨c, ?_, hN.conj_mem a ha.2 c, ?_⟩
    · rw [mem_conjSubgroup]
      simpa [mul_assoc] using ha.1
    · rw [conj_pow, hT.1.2 a ha.1, mul_one, mul_inv_cancel]
  change IsElemAbelian 2 (Subgroup.closure (Group.conjugatesOfSet ((T ⊓ N : Subgroup K) : Set K)))
  refine isElemAbelian_closure_two (fun y hy => (hgen y hy).choose_spec.2.2) fun y hy y' hy' => ?_
  obtain ⟨c, hc, hcN, -⟩ := hgen y hy
  obtain ⟨c', hc', hc'N, -⟩ := hgen y' hy'
  exact mul_comm_of_mem_inf_conj hT hN2 hc hcN hc' hc'N

theorem commutator_mem_normalClosureInf [Finite K] {T N : Subgroup K} (hT : IsWC T)
    [hN : N.Normal] (hN2 : IsPGroup 2 N) (hK : Subgroup.normalClosure (T : Set K) = ⊤) {n : K}
    (hn : n ∈ N) (k : K) : ⁅n, k⁆ ∈ normalClosureInf T N := by
  let D : Subgroup K := (Subgroup.centralizer
    ({QuotientGroup.mk' (normalClosureInf T N) n} : Set (K ⧸ normalClosureInf T N))).comap
      (QuotientGroup.mk' (normalClosureInf T N))
  have hD : ∀ k : K, k ∈ D ↔ ⁅n, k⁆ ∈ normalClosureInf T N := by
    intro k
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h' : QuotientGroup.mk' (normalClosureInf T N) ⁅n, k⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact h.symm
      exact (QuotientGroup.eq_one_iff _).1 h'
    · intro h
      have h' : QuotientGroup.mk' (normalClosureInf T N) ⁅n, k⁆ = 1 :=
        (QuotientGroup.eq_one_iff _).2 h
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h'
      exact h'.symm
  have hsub : Group.conjugatesOfSet (T : Set K) ⊆ (D : Set K) := by
    intro x hx
    obtain ⟨a, ha, hconj⟩ := Group.mem_conjugatesOfSet_iff.1 hx
    obtain ⟨c, rfl⟩ := isConj_iff.1 hconj
    have hxc : c * a * c⁻¹ ∈ conjSubgroup c T := by
      rw [mem_conjSubgroup]
      simpa [mul_assoc] using ha
    have h1 : ⁅n, c * a * c⁻¹⁆ ∈ conjSubgroup c T :=
      comm_mem_of_mem_normalizer (le_normalizer_of_normal_pGroup (hT.conj c) hN2 hn) hxc
    have h2 : ⁅n, c * a * c⁻¹⁆ ∈ N := by
      have : ⁅n, c * a * c⁻¹⁆ = n * ((c * a * c⁻¹) * n⁻¹ * (c * a * c⁻¹)⁻¹) := by
        simp only [commutatorElement_def, mul_assoc]
      rw [this]
      exact N.mul_mem hn (hN.conj_mem n⁻¹ (N.inv_mem hn) _)
    exact (hD _).2 (conjSubgroup_inf_le_normalClosureInf T c ⟨h1, h2⟩)
  have hle : Subgroup.normalClosure (T : Set K) ≤ D := by
    unfold Subgroup.normalClosure
    exact (Subgroup.closure_le D).2 hsub
  rw [hK] at hle
  exact (hD k).1 (hle (Subgroup.mem_top k))

theorem map_le_center_normalClosureInf [Finite K] {T N : Subgroup K} (hT : IsWC T)
    [N.Normal] (hN2 : IsPGroup 2 N) (hK : Subgroup.normalClosure (T : Set K) = ⊤) :
    N.map (QuotientGroup.mk' (normalClosureInf T N)) ≤
      Subgroup.center (K ⧸ normalClosureInf T N) := by
  rintro _ ⟨n, hn, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective g
  have h : QuotientGroup.mk' (normalClosureInf T N) ⁅n, k⁆ = 1 :=
    (QuotientGroup.eq_one_iff _).2 (commutator_mem_normalClosureInf hT hN2 hK hn k)
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h
  exact h.symm

end NormalClosureInf

section BaerSuzukiStep

theorem isPGroup_two_zpowers {x : K} {k : ℕ} (h : x ^ 2 ^ k = 1) :
    IsPGroup 2 (Subgroup.zpowers x) :=
  IsPGroup.of_card_dvd_pow (n := k) (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one h)

theorem isPGroup_two_closure_pair [Finite K] {x y : K} (hxx : x * x = 1) (hyy : y * y = 1)
    (hw : (x * y) ^ 2 ^ 2 = 1) : IsPGroup 2 (Subgroup.closure ({x, y} : Set K)) := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  have hx2 : IsPGroup 2 (Subgroup.zpowers x) :=
    isPGroup_two_zpowers (k := 1) (by simpa [pow_two] using hxx)
  have hw2 : IsPGroup 2 (Subgroup.zpowers (x * y)) := isPGroup_two_zpowers hw
  have hinv : x * (x * y) * x⁻¹ = (x * y)⁻¹ := by
    rw [mul_inv_rev, hxi, hyi, ← mul_assoc, hxx, one_mul]
  have hnorm : x ∈ Subgroup.normalizer ((Subgroup.zpowers (x * y) : Subgroup K) : Set K) := by
    rw [mem_normalizer_iff_conjSubgroup_eq]
    refine conjSubgroup_eq_of_le ?_
    rintro z ⟨u, hu, rfl⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    show x * (x * y) ^ i * x⁻¹ ∈ Subgroup.zpowers (x * y)
    rw [← conj_zpow, hinv]
    exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers _)) i
  have hle : Subgroup.closure ({x, y} : Set K) ≤ Subgroup.zpowers (x * y) ⊔ Subgroup.zpowers x := by
    rw [Subgroup.closure_le]
    intro z hz
    rcases hz with h | h
    · rw [h]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
    · rw [Set.mem_singleton_iff] at h
      rw [h]
      have hmem : x * (x * y) ∈ Subgroup.zpowers (x * y) ⊔ Subgroup.zpowers x :=
        Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
          (Subgroup.mem_sup_left (Subgroup.mem_zpowers (x * y)))
      rwa [← mul_assoc, hxx, one_mul] at hmem
  exact (IsPGroup.to_sup_of_normal_left' hw2 hx2 (Subgroup.zpowers_le.2 hnorm)).to_le hle

theorem isPGroup_two_closure_pair_of_mem_normalizer [Finite K] {T : Subgroup K}
    (hT : IsElemAbelian 2 T) {x y : K} (hx : x ∈ T) (hyy : y * y = 1)
    (hy : y ∈ Subgroup.normalizer (T : Set K)) :
    IsPGroup 2 (Subgroup.closure ({x, y} : Set K)) := by
  have hxx : x * x = 1 := elemAbelian_mul_self hT hx
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  have hcomm : ⁅x, y⁆ ∈ T := by
    rw [← commutatorElement_inv y x]
    exact T.inv_mem (comm_mem_of_mem_normalizer hy hx)
  have hw2 : (x * y) ^ 2 = ⁅x, y⁆ := by
    simp only [commutatorElement_def, hxi, hyi, pow_two, mul_assoc]
  refine isPGroup_two_closure_pair hxx hyy ?_
  rw [show (2 : ℕ) ^ 2 = 2 * 2 from rfl, pow_mul, hw2]
  exact hT.2 _ hcomm

theorem mem_pCore_of_conj_mem_normalizer [Finite K] {T : Subgroup K} (hT : IsElemAbelian 2 T)
    {b : K} (hb : b ∈ T) (hconj : ∀ g : K, g * b * g⁻¹ ∈ Subgroup.normalizer (T : Set K)) :
    b ∈ CFSG.pCore 2 K := by
  have hbb : b * b = 1 := elemAbelian_mul_self hT hb
  refine CFSG.BaerSuzuki.baer_suzuki b
    (isPGroup_two_zpowers (k := 1) (by simpa [pow_two] using hbb)) fun g => ?_
  have hyy : (g * b * g⁻¹) * (g * b * g⁻¹) = 1 := by
    calc (g * b * g⁻¹) * (g * b * g⁻¹) = g * (b * b) * g⁻¹ := by group
      _ = 1 := by rw [hbb]; group
  exact isPGroup_two_closure_pair_of_mem_normalizer hT hb hyy (hconj g)

end BaerSuzukiStep

end CFSG.CGT.Timmesfeld75
