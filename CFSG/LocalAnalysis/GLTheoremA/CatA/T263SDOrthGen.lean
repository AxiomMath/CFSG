module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263SDAut

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.SD

open CFSG.Open
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open scoped commutatorElement Pointwise

section Elements

variable {P : Type} [Group P]

theorem sdo_fixSubgroup_conj (g : P) :
    fixSubgroup (MulAut.conj g) = Subgroup.centralizer ({g} : Set P) := by
  ext h
  rw [mem_fixSubgroup, MulAut.conj_apply, mul_inv_eq_iff_eq_mul,
    Subgroup.mem_centralizer_singleton_iff]
  exact ⟨fun h' => h'.symm, fun h' => h'.symm⟩

theorem sdo_conj_injective (hZ : Subgroup.center P = ⊥) :
    Function.Injective (MulAut.conj : P →* MulAut P) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hc : g ∈ Subgroup.center P := by
    rw [Subgroup.mem_center_iff]
    intro h
    have h1 := congrArg (fun φ : MulAut P => φ h) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  rw [hZ] at hc
  exact Subgroup.mem_bot.1 hc

theorem sdo_famSel_of_elements [Finite P] (p : ℕ) (hZ : Subgroup.center P = ⊥)
    (hEl : ∀ g : P, g ^ p = 1 → g ≠ 1 →
      ∀ B : Subgroup P, (∀ b ∈ B, b ^ p = 1 ∧ b * g = g * b) →
      ∀ Y : Subgroup P, Y ≤ Subgroup.centralizer ({g} : Set P) → IsPGroup 2 ↥Y →
      (∀ b ∈ B, ∀ y ∈ Y, b * y * b⁻¹ ∈ Y) → ⁅B, Y⁆ ≠ ⊥ →
      ∃ J : Subgroup P, IsComponentOf J (Subgroup.centralizer ({g} : Set P)) ∧
        p ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) ∧ ⁅⁅B, Y⁆, J⁆ ≠ ⊥ ∧
        ⁅B, Y⁆ ≤ J ⊔ (Subgroup.centralizer ({g} : Set P) ⊓ Subgroup.centralizer (J : Set P))) :
    FamSel p P (fun φ => φ ∈ Set.range (MulAut.conj : P →* MulAut P)) := by
  have hinj := sdo_conj_injective hZ
  intro u hu hup hu1 𝔹 h𝔹 Y hY hY2 hYB hne
  obtain ⟨g, rfl⟩ := hu
  have hgp : g ^ p = 1 := hinj (by rw [map_pow, hup, map_one])
  have hg1 : g ≠ 1 := fun h => hu1 (by rw [h, map_one])
  set B : Subgroup P := 𝔹.comap (MulAut.conj : P →* MulAut P) with hBdef
  have hB : ∀ b ∈ B, b ^ p = 1 ∧ b * g = g * b := by
    intro b hb
    obtain ⟨-, h1, h2⟩ := h𝔹 _ hb
    exact ⟨hinj (by rw [map_pow, h1, map_one]), hinj (by rw [map_mul, map_mul]; exact h2)⟩
  have hYc : Y ≤ Subgroup.centralizer ({g} : Set P) := by
    rwa [sdo_fixSubgroup_conj] at hY
  have hYB' : ∀ b ∈ B, ∀ y ∈ Y, b * y * b⁻¹ ∈ Y := by
    intro b hb y hy
    have h1 : (MulAut.conj b) y ∈ Y.map (MulAut.conj b).toMonoidHom := Subgroup.mem_map_of_mem _ hy
    rw [hYB _ hb] at h1
    simpa [MulAut.conj_apply] using h1
  have hAC : autComm 𝔹 Y = ⁅B, Y⁆ := by
    unfold autComm
    rw [Subgroup.commutator_def]
    congr 1
    ext z
    constructor
    · rintro ⟨β, hβ, y, hy, rfl⟩
      obtain ⟨b, rfl⟩ := (h𝔹 β hβ).1
      refine ⟨b, hβ, y, hy, ?_⟩
      simp [commutatorElement_def, MulAut.conj_apply]
    · rintro ⟨b, hb, y, hy, rfl⟩
      refine ⟨MulAut.conj b, hb, y, hy, ?_⟩
      simp [commutatorElement_def, MulAut.conj_apply]
  rw [hAC] at hne ⊢
  obtain ⟨J, hJ, hpJ, hc, hle⟩ := hEl g hgp hg1 B hB Y hYc hY2 hYB' hne
  rw [sdo_fixSubgroup_conj]
  exact ⟨J, hJ, hpJ, hc, hle⟩

end Elements

section Commutators

variable {G : Type*} [Group G]

theorem sdo_pow_conj {b y : G} (hbc : b * ⁅b, y⁆ = ⁅b, y⁆ * b) (n : ℕ) :
    b ^ n * y * (b ^ n)⁻¹ = ⁅b, y⁆ ^ n * y := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : b * ⁅b, y⁆ ^ n * b⁻¹ = ⁅b, y⁆ ^ n := by
      rw [mul_inv_eq_iff_eq_mul]
      exact (Commute.pow_right (show Commute b ⁅b, y⁆ from hbc) n).eq
    have h2 : b * y * b⁻¹ = ⁅b, y⁆ * y := by
      simp [commutatorElement_def, mul_assoc]
    calc b ^ (n + 1) * y * (b ^ (n + 1))⁻¹
        = b * (b ^ n * y * (b ^ n)⁻¹) * b⁻¹ := by
          rw [pow_succ', mul_inv_rev]; simp only [mul_assoc]
      _ = b * (⁅b, y⁆ ^ n * y) * b⁻¹ := by rw [ih]
      _ = (b * ⁅b, y⁆ ^ n * b⁻¹) * (b * y * b⁻¹) := by group
      _ = ⁅b, y⁆ ^ n * (⁅b, y⁆ * y) := by rw [h1, h2]
      _ = ⁅b, y⁆ ^ (n + 1) * y := by rw [pow_succ]; simp only [mul_assoc]

theorem sdo_commutator_ne_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {b y : G} (hb : b ^ p = 1)
    (hc2 : ∃ n : ℕ, ⁅b, y⁆ ^ 2 ^ n = 1) (hc1 : ⁅b, y⁆ ≠ 1) : ⁅b, ⁅b, y⁆⁆ ≠ 1 := by
  intro h
  have hbc : b * ⁅b, y⁆ = ⁅b, y⁆ * b := commutatorElement_eq_one_iff_mul_comm.1 h
  have h1 := sdo_pow_conj hbc p
  rw [hb] at h1
  simp only [inv_one, one_mul, mul_one] at h1
  have hcp : ⁅b, y⁆ ^ p = 1 := by
    have := h1.symm
    simpa using this
  obtain ⟨n, hn⟩ := hc2
  have hcop : Nat.Coprime p (2 ^ n) := by
    refine Nat.Coprime.pow_right _ ?_
    exact (Nat.coprime_primes hp Nat.prime_two).2 hp2
  have hd1 : orderOf ⁅b, y⁆ ∣ p := orderOf_dvd_of_pow_eq_one hcp
  have hd2 : orderOf ⁅b, y⁆ ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
  have hd : orderOf ⁅b, y⁆ ∣ Nat.gcd p (2 ^ n) := Nat.dvd_gcd hd1 hd2
  rw [hcop, Nat.dvd_one] at hd
  exact hc1 (orderOf_eq_one_iff.1 hd)

end Commutators

section Select

variable {G : Type*} [Group G] [Finite G]

theorem sdo_odd_order_of_central {ι : Type*} [DecidableEq ι] (J : ι → Subgroup G)
    (hcomm : ∀ i j, i ≠ j → ∀ u ∈ J i, ∀ v ∈ J j, u * v = v * u)
    (hz : ∀ i, ∀ z ∈ J i, (∀ l ∈ J i, z * l = l * z) → ∀ n : ℕ, z ^ 2 ^ n = 1 → z = 1)
    (s : Finset ι) :
    ∀ x ∈ ⨆ i ∈ s, J i, (∀ i ∈ s, ∀ l ∈ J i, x * l = l * x) → Odd (orderOf x) := by
  induction s using Finset.induction_on with
  | empty =>
    intro x hx _
    have h0 : (⨆ i ∈ (∅ : Finset ι), J i) = ⊥ := by simp
    rw [h0, Subgroup.mem_bot] at hx
    rw [hx, orderOf_one]
    exact odd_one
  | insert a s ha ih =>
    intro x hx hxc
    rw [Finset.iSup_insert] at hx
    have hT : (⨆ i ∈ s, J i) ≤ Subgroup.centralizer (J a : Set G) := by
      refine iSup₂_le fun i hi => ?_
      intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      exact hcomm a i (fun h => ha (h ▸ hi)) u hu v hv
    have hmul := Subgroup.coe_mul_of_right_le_normalizer_left (J a) (⨆ i ∈ s, J i)
      (hT.trans (Subgroup.centralizer_le_normalizer _))
    have hx' : x ∈ (J a : Set G) * ((⨆ i ∈ s, J i : Subgroup G) : Set G) := by
      rw [← hmul]
      exact hx
    obtain ⟨y, hy, z, hzs, rfl⟩ := hx'
    have hzc : ∀ i ∈ s, ∀ l ∈ J i, z * l = l * z := by
      intro i hi l hl
      have h1 := hxc i (Finset.mem_insert_of_mem hi) l hl
      have h2 : y * l = l * y := hcomm a i (fun h => ha (h ▸ hi)) y hy l hl
      apply mul_left_cancel (a := y)
      calc y * (z * l) = y * z * l := by rw [mul_assoc]
        _ = l * (y * z) := h1
        _ = (l * y) * z := by rw [mul_assoc]
        _ = (y * l) * z := by rw [h2]
        _ = y * (l * z) := by rw [mul_assoc]
    have hzodd : Odd (orderOf z) := ih z hzs hzc
    have hyz : y * z = z * y := (Subgroup.mem_centralizer_iff.1 (hT hzs) y hy)
    have hyc : ∀ l ∈ J a, y * l = l * y := by
      intro l hl
      have h1 := hxc a (Finset.mem_insert_self a s) l hl
      have h2 : l * z = z * l := Subgroup.mem_centralizer_iff.1 (hT hzs) l hl
      apply mul_right_cancel (b := z)
      calc y * l * z = y * (l * z) := by rw [mul_assoc]
        _ = y * (z * l) := by rw [h2]
        _ = y * z * l := by rw [mul_assoc]
        _ = l * (y * z) := h1
        _ = l * y * z := by rw [mul_assoc]
    have hyodd : Odd (orderOf y) := by
      obtain ⟨k, m, hm, hk⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
      have hym : y ^ m = 1 := by
        refine hz a (y ^ m) (Subgroup.pow_mem _ hy m) (fun l hl => ?_) k ?_
        · exact (Commute.pow_left (show Commute y l from hyc l hl) m).eq
        · rw [← pow_mul, mul_comm, ← hk]
          exact pow_orderOf_eq_one y
      exact hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one hym)
    have hdvd : orderOf (y * z) ∣ Nat.lcm (orderOf y) (orderOf z) :=
      Commute.orderOf_mul_dvd_lcm hyz
    have hodd : Odd (orderOf y * orderOf z) := hyodd.mul hzodd
    exact (hodd.of_dvd_nat ((Nat.lcm_dvd_mul _ _))).of_dvd_nat hdvd

theorem sdo_select_component {ι : Type*} [Finite ι] (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (J : ι → Subgroup G) (C B Y : Subgroup G)
    (hJC : ∀ i, J i ≤ C)
    (hcomm : ∀ i j, i ≠ j → ∀ u ∈ J i, ∀ v ∈ J j, u * v = v * u)
    (hq : ∀ i, J i = ⊥ ∨ IsComponentOf (J i) C)
    (hz : ∀ i, ∀ z ∈ J i, (∀ l ∈ J i, z * l = l * z) → ∀ n : ℕ, z ^ 2 ^ n = 1 → z = 1)
    (hBp : ∀ b ∈ B, b ^ p = 1)
    (hY2 : ∀ y ∈ Y, ∃ n : ℕ, y ^ 2 ^ n = 1)
    (hYB : ∀ b ∈ B, ∀ y ∈ Y, b * y * b⁻¹ ∈ Y)
    (hR : ⁅B, Y⁆ ≤ ⨆ i, J i) (hRne : ⁅B, Y⁆ ≠ ⊥)
    (hinn : ∀ i, p ∣ Nat.card (↥(J i) ⧸ Subgroup.center ↥(J i)) ∨
      ∀ b ∈ B, ∃ c ∈ J i, ∀ l ∈ J i, b * l * b⁻¹ = c * l * c⁻¹) :
    ∃ i, IsComponentOf (J i) C ∧ p ∣ Nat.card (↥(J i) ⧸ Subgroup.center ↥(J i)) ∧
      ⁅⁅B, Y⁆, J i⁆ ≠ ⊥ ∧ ⁅B, Y⁆ ≤ J i ⊔ (C ⊓ Subgroup.centralizer (J i : Set G)) := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  obtain ⟨b₀, hb₀, y₀, hy₀, hz₀⟩ : ∃ b ∈ B, ∃ y ∈ Y, ⁅b, y⁆ ≠ 1 := by
    by_contra hall
    push Not at hall
    apply hRne
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro b hb y hy
    exact Subgroup.mem_bot.2 (hall b hb y hy)
  have hz₀Y : ⁅b₀, y₀⁆ ∈ Y := by
    rw [commutatorElement_def]
    exact Y.mul_mem (hYB b₀ hb₀ y₀ hy₀) (Y.inv_mem hy₀)
  have hw₀ : ⁅b₀, ⁅b₀, y₀⁆⁆ ≠ 1 :=
    sdo_commutator_ne_one hp hp2 (hBp b₀ hb₀) (hY2 _ hz₀Y) hz₀
  have hw₀Y : ⁅b₀, ⁅b₀, y₀⁆⁆ ∈ Y := by
    rw [commutatorElement_def]
    exact Y.mul_mem (hYB b₀ hb₀ _ hz₀Y) (Y.inv_mem hz₀Y)
  have hw₀R : ⁅b₀, ⁅b₀, y₀⁆⁆ ∈ ⁅B, Y⁆ := Subgroup.commutator_mem_commutator hb₀ hz₀Y
  have hz₀R : ⁅b₀, y₀⁆ ∈ ⁅B, Y⁆ := Subgroup.commutator_mem_commutator hb₀ hy₀
  have hnorm : ∀ i, ∀ x ∈ ⨆ k, J k, ∀ l ∈ J i, x * l * x⁻¹ ∈ J i := by
    intro i x hx
    refine Subgroup.iSup_induction J (C := fun x => ∀ l ∈ J i, x * l * x⁻¹ ∈ J i) hx
      (fun k x hxk l hl => ?_) (fun l hl => by simpa using hl) (fun x y hx hy l hl => ?_)
    · by_cases hki : k = i
      · subst hki
        exact (J k).mul_mem ((J k).mul_mem hxk hl) ((J k).inv_mem hxk)
      · have : x * l = l * x := hcomm k i hki x hxk l hl
        rw [this, mul_inv_cancel_right]
        exact hl
    · have := hx _ (hy l hl)
      simpa [mul_assoc] using this
  have hex : ∃ i, ∃ l ∈ J i, ⁅b₀, ⁅b₀, y₀⁆⁆ * l ≠ l * ⁅b₀, ⁅b₀, y₀⁆⁆ := by
    by_contra hnone
    push Not at hnone
    have hmem : ⁅b₀, ⁅b₀, y₀⁆⁆ ∈ ⨆ i ∈ (Finset.univ : Finset ι), J i := by
      have := hR hw₀R
      simpa using this
    have hodd := sdo_odd_order_of_central J hcomm hz Finset.univ _ hmem
      (fun i _ l hl => hnone i l hl)
    obtain ⟨n, hn⟩ := hY2 _ hw₀Y
    have h1 : orderOf ⁅b₀, ⁅b₀, y₀⁆⁆ ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
    have h2 : orderOf ⁅b₀, ⁅b₀, y₀⁆⁆ = 1 :=
      Nat.Coprime.eq_one_of_dvd ((Nat.coprime_two_right.2 hodd).pow_right n) h1
    exact hw₀ (orderOf_eq_one_iff.1 h2)
  obtain ⟨i, l₁, hl₁, hne⟩ := hex
  have hJi : J i ≠ ⊥ := by
    intro h
    rw [h, Subgroup.mem_bot] at hl₁
    exact hne (by rw [hl₁]; simp)
  refine ⟨i, (hq i).resolve_left hJi, ?_, ?_, ?_⟩
  ·
    by_contra hnp
    rcases hinn i with hh | hh
    · exact hnp hh
    obtain ⟨c, hc, hcl⟩ := hh b₀ hb₀
    have hcpow : ∀ n : ℕ, ∀ l ∈ J i, b₀ ^ n * l * (b₀ ^ n)⁻¹ = c ^ n * l * (c ^ n)⁻¹ := by
      intro n
      induction n with
      | zero => intro l hl; simp
      | succ n ih =>
        intro l hl
        have hl' : c ^ n * l * (c ^ n)⁻¹ ∈ J i :=
          (J i).mul_mem ((J i).mul_mem ((J i).pow_mem hc n) hl) ((J i).inv_mem ((J i).pow_mem hc n))
        calc b₀ ^ (n + 1) * l * (b₀ ^ (n + 1))⁻¹
            = b₀ * (b₀ ^ n * l * (b₀ ^ n)⁻¹) * b₀⁻¹ := by
              rw [pow_succ', mul_inv_rev]; simp only [mul_assoc]
          _ = b₀ * (c ^ n * l * (c ^ n)⁻¹) * b₀⁻¹ := by rw [ih l hl]
          _ = c * (c ^ n * l * (c ^ n)⁻¹) * c⁻¹ := hcl _ hl'
          _ = c ^ (n + 1) * l * (c ^ (n + 1))⁻¹ := by
              rw [pow_succ', mul_inv_rev]; simp only [mul_assoc]
    set cc : ↥(J i) := ⟨c, hc⟩ with hcc
    have hcp : cc ^ p ∈ Subgroup.center ↥(J i) := by
      rw [Subgroup.mem_center_iff]
      intro l
      have h1 := hcpow p l.1 l.2
      rw [hBp b₀ hb₀] at h1
      simp only [inv_one, mul_one, one_mul] at h1
      apply Subtype.ext
      show (l : G) * c ^ p = c ^ p * (l : G)
      have h2 : (c ^ p) * (l : G) * (c ^ p)⁻¹ = (l : G) := h1.symm
      rw [mul_inv_eq_iff_eq_mul] at h2
      exact h2.symm
    have hq1 : (QuotientGroup.mk cc : ↥(J i) ⧸ Subgroup.center ↥(J i)) ^ p = 1 := by
      rw [← QuotientGroup.mk_pow]
      exact (QuotientGroup.eq_one_iff _).2 hcp
    have hd1 : orderOf (QuotientGroup.mk cc : ↥(J i) ⧸ Subgroup.center ↥(J i)) ∣ p :=
      orderOf_dvd_of_pow_eq_one hq1
    have hd2 : orderOf (QuotientGroup.mk cc : ↥(J i) ⧸ Subgroup.center ↥(J i)) ∣
        Nat.card (↥(J i) ⧸ Subgroup.center ↥(J i)) := orderOf_dvd_natCard _
    have hcop : Nat.Coprime p (Nat.card (↥(J i) ⧸ Subgroup.center ↥(J i))) :=
      (Nat.Prime.coprime_iff_not_dvd hp).2 hnp
    have hd := Nat.dvd_gcd hd1 hd2
    rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at hd
    have hcz : cc ∈ Subgroup.center ↥(J i) := (QuotientGroup.eq_one_iff _).1 hd
    have hb₀J : ∀ l ∈ J i, b₀ * l = l * b₀ := by
      intro l hl
      have h1 := hcl l hl
      have h2 : c * l * c⁻¹ = l := by
        have := Subgroup.mem_center_iff.1 hcz ⟨l, hl⟩
        have h3 := congrArg Subtype.val this
        simp only [Subgroup.coe_mul] at h3
        rw [mul_inv_eq_iff_eq_mul]
        exact h3.symm
      rw [h2, mul_inv_eq_iff_eq_mul] at h1
      exact h1
    apply hne
    have hl₂ : ⁅b₀, y₀⁆⁻¹ * l₁ * (⁅b₀, y₀⁆⁻¹)⁻¹ ∈ J i := by
      have := hnorm i (⁅b₀, y₀⁆⁻¹) ((⨆ k, J k).inv_mem (hR hz₀R)) l₁ hl₁
      exact this
    have hb₀l₂ : b₀⁻¹ * (⁅b₀, y₀⁆⁻¹ * l₁ * (⁅b₀, y₀⁆⁻¹)⁻¹) =
        (⁅b₀, y₀⁆⁻¹ * l₁ * (⁅b₀, y₀⁆⁻¹)⁻¹) * b₀⁻¹ :=
      (Commute.inv_left (show Commute b₀ _ from hb₀J _ hl₂)).eq
    set z := ⁅b₀, y₀⁆ with hzdef
    set l₂ := z⁻¹ * l₁ * (z⁻¹)⁻¹ with hl₂def
    have e1 : z * l₂ = l₁ * z := by
      rw [hl₂def]; group
    have e2 : b₀ * l₁ = l₁ * b₀ := hb₀J l₁ hl₁
    calc ⁅b₀, z⁆ * l₁ = b₀ * z * b₀⁻¹ * (z⁻¹ * l₁) := by simp [commutatorElement_def, mul_assoc]
      _ = b₀ * z * (b₀⁻¹ * l₂) * z⁻¹ := by rw [hl₂def]; group
      _ = b₀ * z * (l₂ * b₀⁻¹) * z⁻¹ := by rw [hb₀l₂]
      _ = b₀ * (z * l₂) * b₀⁻¹ * z⁻¹ := by group
      _ = b₀ * (l₁ * z) * b₀⁻¹ * z⁻¹ := by rw [e1]
      _ = (b₀ * l₁) * z * b₀⁻¹ * z⁻¹ := by group
      _ = (l₁ * b₀) * z * b₀⁻¹ * z⁻¹ := by rw [e2]
      _ = l₁ * ⁅b₀, z⁆ := by simp [commutatorElement_def, mul_assoc]
  · intro h
    have hmem : ⁅⁅b₀, ⁅b₀, y₀⁆⁆, l₁⁆ ∈ ⁅⁅B, Y⁆, J i⁆ := Subgroup.commutator_mem_commutator hw₀R hl₁
    rw [h, Subgroup.mem_bot] at hmem
    exact hne (commutatorElement_eq_one_iff_mul_comm.1 hmem)
  · refine hR.trans (iSup_le fun k => ?_)
    by_cases hki : k = i
    · subst hki
      exact le_sup_left
    · refine le_sup_of_le_right (le_inf (hJC k) fun v hv => ?_)
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      exact hcomm i k (Ne.symm hki) u hu v hv

end Select

end CFSG.LocalAnalysis.GLTheoremA.T263.SD

end
