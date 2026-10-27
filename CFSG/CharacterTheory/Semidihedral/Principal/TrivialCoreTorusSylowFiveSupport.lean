module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CharacterTheory.Semidihedral.Principal.CyclicInversionAlternatingFive
public import Certificates.Data.A5

public section

open scoped Classical Pointwise

namespace CFSG.Semidihedral.Principal

namespace TrivialCoreTorus

theorem affine_invariant_card_ne_three :
    ∀ d : ZMod 5, ∀ T : Finset (ZMod 5), (∀ a, a ∈ T ↔ 2 * a + 3 * d ∈ T) → T.card ≠ 3 := by
  decide +kernel

theorem exists_odd_perm_conj_eq_sq : ∀ c : Equiv.Perm (Fin 5), c ^ 5 = 1 → c ≠ 1 →
    ∃ d : Equiv.Perm (Fin 5), d * c * d⁻¹ = c ^ 2 ∧ Equiv.Perm.sign d = -1 := by
  decide +kernel

section OrderFive

variable {G : Type*} [Group G]

theorem pow_val_add {w : G} (hw : w ^ 5 = 1) (a b : ZMod 5) :
    w ^ (a + b).val = w ^ a.val * w ^ b.val := by
  rw [ZMod.val_add, ← pow_eq_pow_mod _ hw, pow_add]

theorem pow_val_natCast {w : G} (hw : w ^ 5 = 1) (m : ℕ) : w ^ (m : ZMod 5).val = w ^ m := by
  rw [ZMod.val_natCast, ← pow_eq_pow_mod _ hw]

theorem exists_eq_pow_val_of_mem_zpowers {w x : G} (hw : w ^ 5 = 1)
    (hx : x ∈ Subgroup.zpowers w) : ∃ a : ZMod 5, x = w ^ a.val := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  refine ⟨(k : ZMod 5), ?_⟩
  have hw' : w ^ (5 : ℤ) = 1 := by rw [zpow_ofNat]; exact hw
  have hval : (((k : ZMod 5).val : ℕ) : ℤ) = k % 5 := ZMod.val_intCast k
  rw [← zpow_natCast, hval, ← zpow_eq_zpow_emod k hw']

theorem zpowers_pow_eq {x : G} (hx : x ^ 5 = 1) {k : ℕ} (hk : k % 5 ≠ 0) :
    Subgroup.zpowers (x ^ k) = Subgroup.zpowers x := by
  apply le_antisymm
  · exact Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) k)
  · rw [Subgroup.zpowers_le]
    have h4 : k ^ 4 % 5 = 1 := by
      rw [Nat.pow_mod]
      rcases (show k % 5 = 1 ∨ k % 5 = 2 ∨ k % 5 = 3 ∨ k % 5 = 4 by omega) with h | h | h | h <;>
        rw [h]
    have hx' : (x ^ k) ^ (k ^ 3) = x := by
      rw [← pow_mul, show k * k ^ 3 = k ^ 4 by ring, pow_eq_pow_mod _ hx, h4, pow_one]
    have h := Subgroup.pow_mem _ (Subgroup.mem_zpowers (x ^ k)) (k ^ 3)
    rwa [hx'] at h

theorem pow_five_eq_one_of_pow_eq_one {x : G} {a b : ℕ} (ha : x ^ a = 1) (hb : x ^ b = 1)
    (hab : Nat.gcd a b ∣ 5) : x ^ 5 = 1 :=
  orderOf_dvd_iff_pow_eq_one.mp ((Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one ha)
    (orderOf_dvd_of_pow_eq_one hb)).trans hab)

theorem conj_mem_zpowers_of_conj_mem {w g x : G} (hg : g * w * g⁻¹ ∈ Subgroup.zpowers w)
    (hx : x ∈ Subgroup.zpowers w) : g * x * g⁻¹ ∈ Subgroup.zpowers w := by
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h : g * w ^ j * g⁻¹ = (g * w * g⁻¹) ^ j := by
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
  rw [h]
  exact Subgroup.zpow_mem _ hg j

theorem mem_normalizer_of_forall_conj_mem {P : Subgroup G} [Finite P] {g : G}
    (hg : ∀ x ∈ P, g * x * g⁻¹ ∈ P) : g ∈ Subgroup.normalizer (P : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨hg x, fun hx => ?_⟩
  let f : P → P := fun z => ⟨g * z * g⁻¹, hg z z.2⟩
  have hf : Function.Injective f := by
    intro z₁ z₂ h
    have h' : g * (z₁ : G) * g⁻¹ = g * z₂ * g⁻¹ := congrArg Subtype.val h
    exact Subtype.ext (by simpa using h')
  obtain ⟨z, hz⟩ := Finite.surjective_of_injective hf ⟨g * x * g⁻¹, hx⟩
  have hz' : g * (z : G) * g⁻¹ = g * x * g⁻¹ := congrArg Subtype.val hz
  have hzx : (z : G) = x := by simpa using hz'
  rw [← hzx]
  exact z.2

end OrderFive

theorem exists_order_five_of_cyclic_fifteen {G : Type*} [Group G] (W : Subgroup G)
    (hWcyc : IsCyclic W) (hW15 : Nat.card W = 15) :
    ∃ w ∈ W, orderOf w = 5 ∧ ∀ x ∈ W, x ^ 5 = 1 → x ∈ Subgroup.zpowers w := by
  obtain ⟨g, hg⟩ := hWcyc.exists_generator
  have hgord : orderOf (g : G) = 15 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hW15]
  refine ⟨(g : G) ^ 3, Subgroup.pow_mem _ g.2 3, ?_, ?_⟩
  · rw [orderOf_pow_of_dvd (by norm_num) (by rw [hgord]; norm_num), hgord]
  · intro x hx hx5
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
    have hk' : (g : G) ^ k = x := by
      have h := congrArg Subtype.val hk
      rwa [Subgroup.coe_zpow] at h
    have h15 : ((orderOf (g : G) : ℕ) : ℤ) ∣ k * 5 := by
      rw [orderOf_dvd_iff_zpow_eq_one, zpow_mul, hk', zpow_ofNat, hx5]
    rw [hgord] at h15
    obtain ⟨j, hj⟩ : (3 : ℤ) ∣ k := by omega
    rw [← hk', hj, zpow_mul, zpow_ofNat]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) j

@[expose] def conjOrbit {G : Type*} [Group G] (N L : Subgroup G) : Set (Subgroup G) :=
  {L' | ∃ n ∈ N, L' = L.map (MulAut.conj n).toMonoidHom}

theorem card_eq_ncard_conjOrbit_mul {G : Type*} [Group G] [Finite G] (N L : Subgroup G) :
    Nat.card N =
      (conjOrbit N L).ncard * Nat.card (N ⊓ Subgroup.normalizer (L : Set G) : Subgroup G) := by
  let : MulAction N (Subgroup G) := MulAction.compHom (Subgroup G)
    ((ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom.comp N.subtype)
  have hsmul : ∀ (n : N) (L' : Subgroup G),
      n • L' = L'.map (MulAut.conj (n : G)).toMonoidHom := by
    intro n L'
    change ConjAct.toConjAct (n : G) • L' = _
    rw [Subgroup.pointwise_smul_def]
    congr 1
  have horbit : MulAction.orbit N L = conjOrbit N L := by
    ext L'
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨n, n.2, hsmul n L⟩
    · rintro ⟨n, hn, rfl⟩
      exact ⟨⟨n, hn⟩, hsmul _ L⟩
  have hstab : MulAction.stabilizer N L = (Subgroup.normalizer (L : Set G)).subgroupOf N := by
    ext n
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    change ConjAct.toConjAct (n : G) • L = L ↔ _
    exact Subgroup.conjAct_pointwise_smul_iff
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer N L)
  rw [MulAction.index_stabilizer, horbit, hstab] at h1
  rw [← h1, mul_comm]
  congr 1
  rw [← Subgroup.card_map_of_injective N.subtype_injective, Subgroup.subgroupOf_map_subtype,
    inf_comm]

theorem map_conj_mem_conjOrbit {G : Type*} [Group G] {N L L' : Subgroup G}
    (hL' : L' ∈ conjOrbit N L) {n : G} (hn : n ∈ N) :
    L'.map (MulAut.conj n).toMonoidHom ∈ conjOrbit N L := by
  obtain ⟨m, hm, rfl⟩ := hL'
  refine ⟨n * m, N.mul_mem hn hm, ?_⟩
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem exists_perm_hom_of_torus {G : Type} [Group G] [Finite G] (W : Subgroup G)
    (hodd : Odd (Nat.card W)) (hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a)
    (hKH : (Subgroup.centralizer (W : Set G)).relIndex (Subgroup.normalizer (W : Set G)) = 2)
    (hR : (CFSG.pPrimeCore 2 (Subgroup.centralizer (W : Set G))).map
      (Subgroup.centralizer (W : Set G)).subtype = W)
    (hK : Nonempty ((Subgroup.centralizer (W : Set G) ⧸
      CFSG.pPrimeCore 2 (Subgroup.centralizer (W : Set G))) ≃* alternatingGroup (Fin 5)))
    (hdih : ∃ P : Sylow 2 (Subgroup.normalizer (W : Set G)),
      Nonempty ((P : Subgroup (Subgroup.normalizer (W : Set G))) ≃* DihedralGroup 4)) :
    ∃ σH : Subgroup.normalizer (W : Set G) →* Equiv.Perm (Fin 5), Function.Surjective σH ∧
      (∀ h : Subgroup.normalizer (W : Set G), σH h = 1 ↔ (h : G) ∈ W) ∧
      ∀ h : Subgroup.normalizer (W : Set G),
        (h : G) ∈ Subgroup.centralizer (W : Set G) ↔ σH h ∈ alternatingGroup (Fin 5) := by
  set H := Subgroup.normalizer (W : Set G) with hHdef
  set K := Subgroup.centralizer (W : Set G) with hKdef
  have hWH : W ≤ H := Subgroup.le_normalizer
  have hKH' : K ≤ H := Subgroup.centralizer_le_normalizer _
  set W' : Subgroup H := W.subgroupOf H with hW'def
  have hW'n : W'.Normal := Subgroup.normal_in_normalizer
  have hW'card : Nat.card W' = Nat.card W :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWH).toEquiv
  have hcent : Subgroup.centralizer (W' : Set H) = K.subgroupOf H := by
    ext h
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    constructor
    · intro hh w hw
      exact congrArg Subtype.val (hh ⟨w, hWH hw⟩ hw)
    · intro hh w hw
      exact Subtype.ext (hh w hw)
  have hWK' : W' ≤ Subgroup.centralizer (W' : Set H) := by
    rw [hcent]
    intro x hx
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    intro w hw
    exact hWab w hw _ hx
  have hindex' : (Subgroup.centralizer (W' : Set H)).index = 2 := by
    rw [hcent]
    exact hKH
  let φ : Subgroup.centralizer (W' : Set H) ≃* K :=
    (MulEquiv.subgroupCongr hcent).trans (Subgroup.subgroupOfEquivOfLe hKH')
  have hφval : ∀ x : Subgroup.centralizer (W' : Set H), ((φ x : K) : G) = ((x : H) : G) :=
    fun x => rfl
  have hmapN : (W'.subgroupOf (Subgroup.centralizer (W' : Set H))).map φ.toMonoidHom =
      CFSG.pPrimeCore 2 K := by
    ext k
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxW : ((x : H) : G) ∈ W := hx
      rw [← hR] at hxW
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxW
      have : y = φ.toMonoidHom x := Subtype.ext (by
        change (y : G) = ((φ x : K) : G)
        rw [hφval]
        exact hyx)
      rw [← this]
      exact hy
    · intro hk
      refine ⟨φ.symm k, ?_, by simp⟩
      change (((φ.symm k : Subgroup.centralizer (W' : Set H)) : H) : G) ∈ W
      have h1 : (((φ.symm k : Subgroup.centralizer (W' : Set H)) : H) : G) = (k : G) := by
        rw [← hφval, MulEquiv.apply_symm_apply]
      rw [h1, ← hR]
      exact ⟨k, hk, rfl⟩
  obtain ⟨ψ₀⟩ := hK
  let ψ : Subgroup.centralizer (W' : Set H) ⧸ W'.subgroupOf (Subgroup.centralizer (W' : Set H)) ≃*
      alternatingGroup (Fin 5) := (QuotientGroup.congr _ _ φ hmapN).trans ψ₀
  obtain ⟨P, ⟨eP⟩⟩ := hdih
  obtain ⟨σH, hsurj, hker, hσK⟩ := CyclicAlternatingFive.exists_perm_hom W' (by norm_num)
    CyclicAlternatingFive.autEquiv CyclicAlternatingFive.autEquiv_apply
    CyclicAlternatingFive.alternating_eq_one_of_forall_commute (hW'card ▸ hodd) hWK' hindex' ψ
    P eP
  refine ⟨σH, hsurj, fun h => hker h, fun h => ?_⟩
  rw [← hσK h, hcent, Subgroup.mem_subgroupOf]



theorem ncard_conjOrbit_mod_five_ne_four {G : Type*} [Group G] (N : Subgroup G)
    {w y h : G} {k : ℕ} (hw5 : w ^ 5 = 1) (hy5 : y ^ 5 = 1) (hwy : w * y = y * w)
    (hcover : ∀ n ∈ N, Subgroup.zpowers (n * w * n⁻¹) = Subgroup.zpowers w ∨
      ∃ a : ZMod 5, Subgroup.zpowers (n * w * n⁻¹) = Subgroup.zpowers (y * w ^ a.val))
    (hne : ∀ a : ZMod 5, Subgroup.zpowers (y * w ^ a.val) ≠ Subgroup.zpowers w)
    (hinj : ∀ a b : ZMod 5, Subgroup.zpowers (y * w ^ a.val) =
      Subgroup.zpowers (y * w ^ b.val) → a = b)
    (hhN : h ∈ N) (hhw : h * w * h⁻¹ = w⁻¹) (hhy : h * y * h⁻¹ = y ^ 2 * w ^ k) :
    (conjOrbit N (Subgroup.zpowers w)).ncard % 5 ≠ 4 := by
  set O := conjOrbit N (Subgroup.zpowers w) with hOdef
  set L : ZMod 5 → Subgroup G := fun a => Subgroup.zpowers (y * w ^ a.val) with hLdef
  set T : Finset (ZMod 5) := Finset.univ.filter (fun a => L a ∈ O) with hTdef
  have hwinv : w⁻¹ = w ^ 4 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ', hw5])
  have hcomm : ∀ i j : ℕ, Commute (y ^ i) (w ^ j) := fun i j =>
    (show Commute w y from hwy).symm.pow_pow i j
  have hconj : ∀ m : ℕ, h * (y * w ^ m) * h⁻¹ = y ^ 2 * w ^ (k + 4 * m) := by
    intro m
    have h1 : h * w ^ m * h⁻¹ = w ^ (4 * m) := by
      rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply, hhw, hwinv, ← pow_mul]
    calc h * (y * w ^ m) * h⁻¹ = (h * y * h⁻¹) * (h * w ^ m * h⁻¹) := by group
      _ = y ^ 2 * w ^ (k + 4 * m) := by rw [hhy, h1, mul_assoc, ← pow_add]
  have hcube : ∀ m : ℕ, (y ^ 2 * w ^ (k + 4 * m)) ^ 3 = y * w ^ (3 * k + 12 * m) := by
    intro m
    rw [(hcomm 2 (k + 4 * m)).mul_pow, ← pow_mul, ← pow_mul,
      show 2 * 3 = 5 + 1 by norm_num, pow_add, hy5, one_mul, pow_one]
    congr 2
    ring
  have hfive : ∀ m : ℕ, (y ^ 2 * w ^ (k + 4 * m)) ^ 5 = 1 := by
    intro m
    rw [(hcomm 2 (k + 4 * m)).mul_pow, ← pow_mul, ← pow_mul, show 2 * 5 = 5 * 2 by norm_num,
      pow_mul, hy5, one_pow, one_mul, mul_comm, pow_mul, hw5, one_pow]
  have hval : ∀ a : ZMod 5, w ^ (2 * a + 3 * (k : ZMod 5)).val = w ^ (3 * k + 12 * a.val) := by
    intro a
    rw [pow_eq_pow_mod _ hw5, pow_eq_pow_mod (3 * k + 12 * a.val) hw5]
    congr 1
    rw [ZMod.val_add, ZMod.val_mul, ZMod.val_mul, ZMod.val_natCast,
      show (2 : ZMod 5).val = 2 from rfl, show (3 : ZMod 5).val = 3 from rfl]
    omega
  have hτ : ∀ a : ZMod 5, (L a).map (MulAut.conj h).toMonoidHom = L (2 * a + 3 * (k : ZMod 5)) := by
    intro a
    simp only [hLdef]
    rw [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hconj,
      ← zpowers_pow_eq (hfive a.val) (k := 3) (by norm_num), hcube, hval]
  have hconjinv : ∀ L' : Subgroup G, (L'.map (MulAut.conj h).toMonoidHom).map
      (MulAut.conj h⁻¹).toMonoidHom = L' := by
    intro L'
    rw [Subgroup.map_map]
    conv_rhs => rw [← Subgroup.map_id L']
    congr 1
    ext x
    simp [mul_assoc]
  have hOinv : ∀ a, L a ∈ O ↔ L (2 * a + 3 * (k : ZMod 5)) ∈ O := by
    intro a
    constructor
    · intro ha
      rw [← hτ a]
      exact map_conj_mem_conjOrbit ha hhN
    · intro ha
      have h1 := map_conj_mem_conjOrbit ha (N.inv_mem hhN)
      rwa [← hτ a, hconjinv] at h1
  have hTinv : ∀ a, a ∈ T ↔ 2 * a + 3 * (k : ZMod 5) ∈ T := by
    intro a
    simp only [hTdef, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hOinv a
  have hT3 : T.card ≠ 3 := affine_invariant_card_ne_three _ T hTinv
  have hT5 : T.card ≤ 5 := by
    have h := Finset.card_le_univ T
    rwa [ZMod.card] at h
  have hO : O = insert (Subgroup.zpowers w) (L '' (T : Set (ZMod 5))) := by
    ext L'
    constructor
    · intro hL'
      have hL'O := hL'
      obtain ⟨n, hn, rfl⟩ := hL'
      rw [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hL'O ⊢
      rcases hcover n hn with h1 | ⟨a, ha⟩
      · exact Or.inl h1
      · refine Or.inr ⟨a, Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩),
          ha.symm⟩
        change Subgroup.zpowers (y * w ^ a.val) ∈ O
        rw [← ha]
        exact hL'O
    · rintro (rfl | ⟨a, ha, rfl⟩)
      · refine ⟨1, N.one_mem, ?_⟩
        rw [map_one]
        conv_lhs => rw [← Subgroup.map_id (Subgroup.zpowers w)]
        rfl
      · exact (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
  have hcard : O.ncard = T.card + 1 := by
    have hnot : Subgroup.zpowers w ∉ L '' (T : Set (ZMod 5)) := by
      rintro ⟨a, -, ha⟩
      exact hne a ha
    have hLinj : Function.Injective L := fun a b hab => hinj a b hab
    rw [hO, Set.ncard_insert_of_notMem hnot, Set.ncard_image_of_injective _ hLinj,
      Set.ncard_coe_finset]
  omega

theorem factorization_five_twentyfive_mul {m : ℕ} (hm : ¬ 5 ∣ m) :
    (25 * m).factorization 5 = 2 := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero 5)
  rw [Nat.factorization_mul (by norm_num) hm0, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hm, show (25 : ℕ) = 5 ^ 2 by norm_num,
    Nat.Prime.factorization_pow Nat.prime_five, Finsupp.single_eq_same]

theorem ncard_conjOrbit_mod_five {G : Type} [Group G] [Finite G] (H P L : Subgroup G)
    (hPH : P ≤ H) (hP : Nat.card P = 25) (hH : Nat.card H = 1800)
    (M : ℕ) (hG : Nat.card G = 1800 * M) (hM : ¬ 5 ∣ M)
    (hstab : ∀ n ∈ Subgroup.normalizer (P : Set G),
      n ∈ Subgroup.normalizer (L : Set G) ↔ n ∈ H) :
    (conjOrbit (Subgroup.normalizer (P : Set G)) L).ncard % 5 = M % 5 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hfacG : (Nat.card G).factorization 5 = 2 := by
    rw [hG, show 1800 * M = 25 * (72 * M) by ring]
    exact factorization_five_twentyfive_mul (by omega)
  have hfacH : (Nat.card H).factorization 5 = 2 := by
    rw [hH, show (1800 : ℕ) = 25 * 72 by norm_num]
    exact factorization_five_twentyfive_mul (by norm_num)
  have hPHcard : Nat.card (P.subgroupOf H) = 25 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPH).toEquiv, hP]
  let SG : Sylow 5 G := Sylow.ofCard P (by rw [hP, hfacG]; norm_num)
  let SH : Sylow 5 H := Sylow.ofCard (P.subgroupOf H) (by rw [hPHcard, hfacH]; norm_num)
  have hnG : Nat.card (Sylow 5 G) = (Subgroup.normalizer (P : Set G)).index := by
    rw [Sylow.card_eq_index_normalizer SG]
    rfl
  have hnH : Nat.card (Sylow 5 H) = ((Subgroup.normalizer (P : Set G)).subgroupOf H).index := by
    rw [Sylow.card_eq_index_normalizer SH, Subgroup.subgroupOf_normalizer_eq hPH]
    rfl
  have hmodG : Nat.card (Sylow 5 G) % 5 = 1 := card_sylow_modEq_one (p := 5) (G := G)
  have hmodH : Nat.card (Sylow 5 H) % 5 = 1 := card_sylow_modEq_one (p := 5) (G := H)
  set NG := Subgroup.normalizer (P : Set G) with hNGdef
  have h1 := Subgroup.card_mul_index NG
  have h2 := Subgroup.card_mul_index (NG.subgroupOf H)
  have hcardNH : Nat.card (NG.subgroupOf H) = Nat.card (NG ⊓ H : Subgroup G) := by
    rw [← Subgroup.card_map_of_injective H.subtype_injective, Subgroup.subgroupOf_map_subtype]
  have h3 := card_eq_ncard_conjOrbit_mul NG L
  have hinf : NG ⊓ Subgroup.normalizer (L : Set G) = NG ⊓ H := by
    ext n
    simp only [Subgroup.mem_inf]
    exact ⟨fun h => ⟨h.1, (hstab n h.1).mp h.2⟩, fun h => ⟨h.1, (hstab n h.1).mpr h.2⟩⟩
  rw [hinf] at h3
  rw [hcardNH, ← hnH, hH] at h2
  rw [← hnG, hG, h3] at h1
  set X := Nat.card (NG ⊓ H : Subgroup G)
  set O := (conjOrbit NG L).ncard
  have hX : 0 < X := Nat.card_pos
  have heq : O * Nat.card (Sylow 5 G) = Nat.card (Sylow 5 H) * M := by
    have h4 : X * (O * Nat.card (Sylow 5 G)) = X * (Nat.card (Sylow 5 H) * M) := by
      calc X * (O * Nat.card (Sylow 5 G)) = O * X * Nat.card (Sylow 5 G) := by ring
        _ = 1800 * M := h1
        _ = X * Nat.card (Sylow 5 H) * M := by rw [h2]
        _ = X * (Nat.card (Sylow 5 H) * M) := by ring
    exact Nat.eq_of_mul_eq_mul_left hX h4
  have h5 := congrArg (· % 5) heq
  rw [Nat.mul_mod, hmodG, Nat.mul_mod (Nat.card (Sylow 5 H)), hmodH] at h5
  omega

theorem exists_sylow_five_of_torus {G : Type} [Group G] [Finite G] (W : Subgroup G)
    (hWcyc : IsCyclic W) (hW15 : Nat.card W = 15)
    (hK : Nat.card (Subgroup.centralizer (W : Set G)) = 900) :
    ∃ (P : Subgroup G) (w : G), P ≤ Subgroup.centralizer (W : Set G) ∧ Nat.card P = 25 ∧
      w ∈ W ∧ w ∈ P ∧ orderOf w = 5 ∧ ∀ x ∈ W, x ^ 5 = 1 → x ∈ Subgroup.zpowers w := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set K := Subgroup.centralizer (W : Set G) with hKdef
  obtain ⟨w, hwW, hword, hW5⟩ := exists_order_five_of_cyclic_fifteen W hWcyc hW15
  have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((IsCyclic.isMulCommutative (α := W)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hWK : W ≤ K := fun v hv => Subgroup.mem_centralizer_iff.mpr fun x hx => hWab x hx v hv
  obtain ⟨Q⟩ : Nonempty (Sylow 5 K) := inferInstance
  have hQ : Nat.card Q = 25 := by
    rw [Sylow.card_eq_multiplicity, hK, show (900 : ℕ) = 25 * 36 by norm_num,
      factorization_five_twentyfive_mul (by norm_num)]
    norm_num
  have hwK : w ∈ K := hWK hwW
  have hzK : Subgroup.zpowers w ≤ K := Subgroup.zpowers_le.mpr hwK
  have hnorm : ((Subgroup.zpowers w).subgroupOf K).Normal := by
    constructor
    intro x hx k
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have hxW : (x : G) ∈ W := (Subgroup.zpowers_le.mpr hwW) hx
    have hc : (x : G) * k = k * x := Subgroup.mem_centralizer_iff.mp k.2 x hxW
    have h' : ((k * x * k⁻¹ : K) : G) = x := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hc, mul_inv_cancel_right]
    rw [h']
    exact hx
  have hp : IsPGroup 5 ((Subgroup.zpowers w).subgroupOf K) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzK).toEquiv, Nat.card_zpowers, hword,
        pow_one])
  have hle := hp.le_sylow_of_normal Q
  refine ⟨(Q : Subgroup K).map K.subtype, w, Subgroup.map_subtype_le _,
    by rw [Subgroup.card_map_of_injective K.subtype_injective, hQ], hwW, ?_, hword, hW5⟩
  exact ⟨⟨w, hwK⟩, hle (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers w)), rfl⟩

end TrivialCoreTorus

end CFSG.Semidihedral.Principal
