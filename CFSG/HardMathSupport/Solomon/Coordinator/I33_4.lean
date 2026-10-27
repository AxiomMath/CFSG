module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Basic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.UniquenessMaximal

section FourGroup

variable {G : Type} [Group G] [Finite G]

theorem i334_mem_four {U : Subgroup G} (hU : IsPPlane 2 U) {b z : G} (hb : b ∈ U) (hz : z ∈ U)
    (hb1 : b ≠ 1) (hz1 : z ≠ 1) (hbz : b ≠ z) {x : G} (hx : x ∈ U) :
    x = 1 ∨ x = b ∨ x = z ∨ x = b * z := by
  classical
  obtain ⟨-, hsq⟩ := hU.1
  have hcard := hU.2
  have hb2 : b ^ 2 = 1 := hsq b hb
  have hz2 : z ^ 2 = 1 := hsq z hz
  have hbzU : b * z ∈ U := U.mul_mem hb hz
  have hzinv : z⁻¹ = z := by
    rw [inv_eq_iff_mul_eq_one, ← sq, hz2]
  have hbinv : b⁻¹ = b := by
    rw [inv_eq_iff_mul_eq_one, ← sq, hb2]
  have hne1 : b * z ≠ 1 := by
    intro h
    apply hbz
    rw [mul_eq_one_iff_eq_inv.1 h, hzinv]
  have hbne : b * z ≠ b := fun h => hz1 (by simpa using h)
  have hzne : b * z ≠ z := fun h => hb1 (by simpa using h)
  let f : Fin 4 → U := ![⟨1, U.one_mem⟩, ⟨b, hb⟩, ⟨z, hz⟩, ⟨b * z, hbzU⟩]
  have hinj : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
      | rfl
      | (exfalso
         simp only [f, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
           Matrix.cons_val_one, Matrix.cons_val, Subtype.mk.injEq] at hij
         first
         | exact hb1 hij.symm
         | exact hb1 hij
         | exact hz1 hij.symm
         | exact hz1 hij
         | exact hne1 hij.symm
         | exact hne1 hij
         | exact hbz hij
         | exact hbz hij.symm
         | exact hbne hij
         | exact hbne hij.symm
         | exact hzne hij
         | exact hzne hij.symm)
  have hbij : Function.Bijective f := by
    refine hinj.bijective_of_nat_card_le ?_
    rw [Nat.card_eq_fintype_card (α := Fin 4), Fintype.card_fin]
    exact hcard.le.trans (by norm_num)
  obtain ⟨i, hi⟩ := hbij.2 ⟨x, hx⟩
  fin_cases i <;> simp only [f, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, Subtype.ext_iff] at hi <;> tauto

omit [Finite G] in
theorem i334_comm {U : Subgroup G} (hU : IsPPlane 2 U) {x y : G} (hx : x ∈ U) (hy : y ∈ U) :
    x * y = y * x :=
  congrArg Subtype.val (hU.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

omit [Finite G] in
theorem i334_inv_eq {U : Subgroup G} (hU : IsPPlane 2 U) {x : G} (hx : x ∈ U) : x⁻¹ = x := by
  rw [inv_eq_iff_mul_eq_one, ← sq, hU.1.2 x hx]

omit [Finite G] in
theorem i334_mem_zpowers {b z : G} (hb : b ^ 2 = 1) (hz : z ∈ Subgroup.zpowers b) :
    z = 1 ∨ z = b := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  rcases Int.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · left
    rw [hk, ← two_mul, zpow_mul]
    simp [hb]
  · right
    rw [hk, zpow_add, zpow_mul]
    simp [hb]

theorem i334_conj_fix {U : Subgroup G} (hU : IsPPlane 2 U) {b g : G} (hb : b ∈ U) (hb1 : b ≠ 1)
    (hgU : ∀ x ∈ U, g * x * g⁻¹ ∈ U) (hgb : g * b * g⁻¹ = b) {u : G} (hu : u ∈ U) :
    g * u * g⁻¹ = u ∨ g * u * g⁻¹ = u * b := by
  by_cases hu1 : u = 1
  · left
    simp [hu1]
  by_cases hub : u = b
  · left
    rw [hub, hgb]
  have hmem := i334_mem_four hU hb hu hb1 hu1 (Ne.symm hub) (hgU u hu)
  rcases hmem with h | h | h | h
  · exfalso
    exact hu1 (by simpa using h)
  · exfalso
    apply hub
    have : g * u * g⁻¹ = g * b * g⁻¹ := h.trans hgb.symm
    simpa using this
  · left
    exact h
  · right
    rw [h, i334_comm hU hb hu]

end FourGroup

section TwoLocal

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem i334_centralizer_eq {b : G} (hb1 : b ≠ 1) (hb2 : b ^ 2 = 1) :
    Subgroup.centralizer ({b} : Set G) = Subgroup.normalizer (Subgroup.zpowers b : Set G) := by
  ext g
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h x
    simp only [Set.mem_singleton_iff, forall_eq] at h
    have hg : g * b * g⁻¹ = b := by rw [mul_inv_eq_iff_eq_mul, h]
    constructor
    · rintro hx
      rcases i334_mem_zpowers hb2 hx with rfl | rfl
      · simp
      · rw [hg]
        exact Subgroup.mem_zpowers _
    · intro hx
      rcases i334_mem_zpowers hb2 hx with h1 | h1
      · have : x = 1 := by
          have := congrArg (fun w => g⁻¹ * w * g) h1
          simpa [mul_assoc] using this
        rw [this]
        exact Subgroup.one_mem _
      · have : x = b := by
          have h2 := congrArg (fun w => g⁻¹ * w * g) h1
          have h3 : g⁻¹ * b * g = b := by
            rw [mul_assoc, h, inv_mul_cancel_left]
          simpa [mul_assoc, h3] using h2
        rw [this]
        exact Subgroup.mem_zpowers _
  · intro h
    simp only [Set.mem_singleton_iff, forall_eq]
    have h1 := (h b).1 (Subgroup.mem_zpowers b)
    rcases i334_mem_zpowers hb2 h1 with h2 | h2
    · exfalso
      apply hb1
      simpa using h2
    · rw [mul_inv_eq_iff_eq_mul] at h2
      exact h2.symm

omit [Finite G] in
theorem i334_conj_zpowers {b y z : G} (hy : y ∈ Subgroup.centralizer ({b} : Set G))
    (hz : z ∈ Subgroup.zpowers b) : y * z * y⁻¹ = z := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  have hc : Commute y b := (Subgroup.mem_centralizer_iff.1 hy b rfl).symm
  rw [mul_inv_eq_iff_eq_mul]
  exact (hc.zpow_right n).eq

def i334K (b : G) (Q : Subgroup G) : Subgroup G where
  carrier := {y | y ∈ Subgroup.centralizer ({b} : Set G) ∧
    ∀ q ∈ Q, q * y * q⁻¹ * y⁻¹ ∈ Subgroup.zpowers b}
  one_mem' := ⟨Subgroup.one_mem _, fun q _ => by simp⟩
  mul_mem' := by
    rintro y1 y2 ⟨hy1, h1⟩ ⟨hy2, h2⟩
    refine ⟨Subgroup.mul_mem _ hy1 hy2, fun q hq => ?_⟩
    have e : q * (y1 * y2) * q⁻¹ * (y1 * y2)⁻¹ =
        (q * y1 * q⁻¹ * y1⁻¹) * (y1 * (q * y2 * q⁻¹ * y2⁻¹) * y1⁻¹) := by group
    rw [e, i334_conj_zpowers hy1 (h2 q hq)]
    exact Subgroup.mul_mem _ (h1 q hq) (h2 q hq)
  inv_mem' := by
    rintro y ⟨hy, h⟩
    refine ⟨Subgroup.inv_mem _ hy, fun q hq => ?_⟩
    have e : q * y⁻¹ * q⁻¹ * (y⁻¹)⁻¹ =
        y⁻¹ * (q * y * q⁻¹ * y⁻¹)⁻¹ * (y⁻¹)⁻¹ := by group
    rw [e, i334_conj_zpowers (Subgroup.inv_mem _ hy) (Subgroup.inv_mem _ (h q hq))]
    exact Subgroup.inv_mem _ (h q hq)

omit [Finite G] in
theorem i334_isTwoLocal {b : G} (hb1 : b ≠ 1) (hb2 : b ^ 2 = 1) :
    IsTwoLocal (Subgroup.centralizer ({b} : Set G)) := by
  refine ⟨Subgroup.zpowers b, ?_, ?_, i334_centralizer_eq hb1 hb2⟩
  · intro h
    apply hb1
    have : b ∈ Subgroup.zpowers b := Subgroup.mem_zpowers b
    rw [h] at this
    simpa using this
  · refine fun x => ⟨1, ?_⟩
    obtain ⟨x, hx⟩ := x
    rcases i334_mem_zpowers hb2 hx with rfl | rfl
    · ext
      simp
    · ext
      simpa using hb2

theorem i334_le_pCore (hchar : IsCharTwoType G) {U : Subgroup G} (hU : IsPPlane 2 U) {b : G}
    (hb : b ∈ U) (hb1 : b ≠ 1)
    (hQ : pCoreOf 2 (Subgroup.centralizer ({b} : Set G)) ≤ Subgroup.normalizer (U : Set G)) :
    U ≤ pCoreOf 2 (Subgroup.centralizer ({b} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hb2 : b ^ 2 = 1 := hU.1.2 b hb
  set C : Subgroup G := Subgroup.centralizer ({b} : Set G) with hC
  set Q : Subgroup G := pCoreOf 2 C with hQdef
  have hCQ : C ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 C
  have hQpg : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 C
  have hchar' := hchar C (i334_isTwoLocal hb1 hb2)
  have hKC : i334K b Q ≤ C := fun y hy => hy.1
  have key : ∀ c ∈ C, ∀ y ∈ i334K b Q, c * y * c⁻¹ ∈ i334K b Q := by
    intro c hc y ⟨hy, h⟩
    refine ⟨?_, fun q hq => ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hc hy) (Subgroup.inv_mem _ hc)
    · have hq' : c⁻¹ * q * c ∈ Q := by
        have := (Subgroup.mem_normalizer_iff.1 (hCQ (Subgroup.inv_mem _ hc)) q).1 hq
        simpa using this
      have e : q * (c * y * c⁻¹) * q⁻¹ * (c * y * c⁻¹)⁻¹ =
          c * ((c⁻¹ * q * c) * y * (c⁻¹ * q * c)⁻¹ * y⁻¹) * c⁻¹ := by group
      rw [e, i334_conj_zpowers hc (h _ hq')]
      exact h _ hq'
  have hKn : C ≤ Subgroup.normalizer (i334K b Q : Set G) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨key c hc x, fun hx => ?_⟩
    have := key c⁻¹ (Subgroup.inv_mem _ hc) _ hx
    simpa [mul_assoc] using this
  have hK2 : IsPGroup 2 (i334K b Q) := by
    rintro ⟨y, hy, h⟩
    have hsq : y * y ∈ Q := by
      refine hchar' ⟨Subgroup.mul_mem _ hy hy, Subgroup.mem_centralizer_iff.2 ?_⟩
      intro q hq
      have hz := h q hq
      have hyz : y * (q * y * q⁻¹ * y⁻¹) = (q * y * q⁻¹ * y⁻¹) * y := by
        have := i334_conj_zpowers hy hz
        rwa [mul_inv_eq_iff_eq_mul] at this
      have hzz : (q * y * q⁻¹ * y⁻¹) * (q * y * q⁻¹ * y⁻¹) = 1 := by
        rcases i334_mem_zpowers hb2 hz with h1 | h1
        · rw [h1, one_mul]
        · rw [h1, ← sq, hb2]
      have hqy : q * y * q⁻¹ = (q * y * q⁻¹ * y⁻¹) * y := by group
      have e : q * (y * y) * q⁻¹ = y * y := by
        calc q * (y * y) * q⁻¹ = (q * y * q⁻¹) * (q * y * q⁻¹) := by group
          _ = ((q * y * q⁻¹ * y⁻¹) * y) * ((q * y * q⁻¹ * y⁻¹) * y) := by rw [← hqy]
          _ = (q * y * q⁻¹ * y⁻¹) * (y * (q * y * q⁻¹ * y⁻¹)) * y := by group
          _ = (q * y * q⁻¹ * y⁻¹) * ((q * y * q⁻¹ * y⁻¹) * y) * y := by rw [hyz]
          _ = ((q * y * q⁻¹ * y⁻¹) * (q * y * q⁻¹ * y⁻¹)) * (y * y) := by group
          _ = y * y := by rw [hzz, one_mul]
      rwa [mul_inv_eq_iff_eq_mul] at e
    obtain ⟨k, hk⟩ := hQpg ⟨y * y, hsq⟩
    have hk' : (y * y) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    refine ⟨k + 1, Subtype.ext ?_⟩
    change y ^ 2 ^ (k + 1) = 1
    rw [pow_succ', pow_mul, sq]
    exact hk'
  have hKle := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hKC hKn hK2
  intro u hu
  refine hKle ⟨?_, fun q hq => ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact i334_comm hU hb hu
  · have hqn := hQ hq
    have hqC : q ∈ C := CFSG.LieType.BorelTits.pCoreOf_le 2 C hq
    have hqb : q * b * q⁻¹ = b := by
      rw [mul_inv_eq_iff_eq_mul]
      exact (Subgroup.mem_centralizer_iff.1 hqC b rfl).symm
    have hqU : ∀ x ∈ U, q * x * q⁻¹ ∈ U := fun x hx =>
      (Subgroup.mem_normalizer_iff.1 hqn x).1 hx
    rcases i334_conj_fix hU hb hb1 hqU hqb hu with h | h
    · rw [h]
      simp
    · rw [h, i334_comm hU hu hb, mul_inv_cancel_right]
      exact Subgroup.mem_zpowers b

omit [Finite G] in
theorem i334_eq_one_of_mem_odd {Q Y : Subgroup G} (hQ : IsPGroup 2 Q) (hY : ¬ 2 ∣ Nat.card Y)
    {w : G} (hwQ : w ∈ Q) (hwY : w ∈ Y) : w = 1 := by
  obtain ⟨k, hk⟩ := hQ ⟨w, hwQ⟩
  have hk' : w ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 : orderOf w ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  have h2 : orderOf w ∣ Nat.card Y := by
    have := Subgroup.orderOf_dvd_natCard Y hwY
    simpa using this
  rcases j with _ | j
  · simpa using hj
  · exfalso
    apply hY
    refine (dvd_pow_self 2 (Nat.succ_ne_zero j)).trans ?_
    rw [← hj]
    exact h2

theorem i334_centralizes {U Y : Subgroup G} (hU : IsPPlane 2 U)
    (hUQ : ∀ b ∈ U, b ≠ 1 → U ≤ pCoreOf 2 (Subgroup.centralizer ({b} : Set G)))
    (hY : ¬ 2 ∣ Nat.card Y) (hUY : U ≤ Subgroup.normalizer (Y : Set G)) :
    U ≤ Subgroup.centralizer (Y : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial U := by
    refine Finite.one_lt_card_iff_nontrivial.1 ?_
    rw [hU.2]
    norm_num
  have hgen := le_iSup_inf_centralizer_hyperplane hU.1 hUY hY
  have hle : (⨆ (K : Subgroup G) (_ : K ≤ U ∧ (K.subgroupOf U).index = 2),
      Y ⊓ Subgroup.centralizer (K : Set G)) ≤ Subgroup.centralizer (U : Set G) := by
    refine iSup_le fun K => iSup_le fun hK => ?_
    have hKcard : Nat.card K = 2 ^ 1 := card_eq_of_index_eq Nat.prime_two hK.1 hK.2 (n := 1) hU.2
    have hKne : K ≠ ⊥ := by
      intro h
      rw [h] at hKcard
      simp at hKcard
    obtain ⟨⟨b, hbK⟩, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hKne
    have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
    have hbU : b ∈ U := hK.1 hbK
    have hUb := hUQ b hbU hb1'
    rintro y ⟨hyY, hyK⟩
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hyC : y ∈ Subgroup.centralizer ({b} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact Subgroup.mem_centralizer_iff.1 hyK x hbK
    have hQnorm := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2
      (Subgroup.centralizer ({b} : Set G))
    have h1 : y * u * y⁻¹ * u⁻¹ ∈ pCoreOf 2 (Subgroup.centralizer ({b} : Set G)) := by
      refine Subgroup.mul_mem _ ?_ (Subgroup.inv_mem _ (hUb hu))
      have := (Subgroup.mem_normalizer_iff.1 (hQnorm hyC) u).1 (hUb hu)
      exact this
    have h2 : y * u * y⁻¹ * u⁻¹ ∈ Y := by
      have e : y * u * y⁻¹ * u⁻¹ = y * (u * y⁻¹ * u⁻¹) := by group
      rw [e]
      refine Subgroup.mul_mem _ hyY ?_
      exact (Subgroup.mem_normalizer_iff.1 (hUY hu) y⁻¹).1 (Subgroup.inv_mem _ hyY)
    have h3 := i334_eq_one_of_mem_odd (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) hY h1 h2
    have h4 : y * u = u * y := mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h3)
    exact h4.symm
  intro u hu
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hyU := Subgroup.mem_centralizer_iff.1 (hle (hgen hy)) u hu
  exact hyU.symm

end TwoLocal

section Sylow

variable {G : Type} [Group G] [Finite G]

theorem i334_exists_central {T U : Subgroup G} (hT : IsPGroup 2 T)
    (hTU : ∀ t ∈ T, ∀ x ∈ U, t * x * t⁻¹ ∈ U) (hUT : U ≤ T) (hU1 : U ≠ ⊥) :
    ∃ Z ∈ U, Z ≠ 1 ∧ ∀ x ∈ T, x * Z * x⁻¹ = Z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent T := hT.isNilpotent
  have hN : (U.subgroupOf T).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hTU g g.2 n hn⟩
  have hne : U.subgroupOf T ≠ ⊥ := by
    intro h
    apply hU1
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hUT hx⟩ : T) ∈ U.subgroupOf T := hx
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
  obtain ⟨⟨z, hz⟩, hz1⟩ :=
    (Subgroup.ne_bot_iff_exists_ne_one).1 (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  obtain ⟨hzU, hzc⟩ := Subgroup.mem_inf.1 hz
  refine ⟨(z : G), hzU, fun h => hz1 (Subtype.ext (Subtype.ext h)), fun x hx => ?_⟩
  have := Subgroup.mem_center_iff.1 hzc ⟨x, hx⟩
  rw [mul_inv_eq_iff_eq_mul]
  exact congrArg Subtype.val this

omit [Finite G] in
def i334Omega (T : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ T ∧ (∀ y ∈ T, y * x * y⁻¹ = x) ∧ x ^ 2 = 1}
  one_mem' := ⟨T.one_mem, fun y _ => by simp, by simp⟩
  mul_mem' := by
    rintro x1 x2 ⟨h1T, h1c, h12⟩ ⟨h2T, h2c, h22⟩
    refine ⟨T.mul_mem h1T h2T, fun y hy => ?_, ?_⟩
    · have : y * (x1 * x2) * y⁻¹ = (y * x1 * y⁻¹) * (y * x2 * y⁻¹) := by group
      rw [this, h1c y hy, h2c y hy]
    · have hc : Commute x1 x2 := by
        have := h2c x1 h1T
        exact mul_inv_eq_iff_eq_mul.1 this
      rw [hc.mul_pow, h12, h22, one_mul]
  inv_mem' := by
    rintro x ⟨hxT, hxc, hx2⟩
    refine ⟨T.inv_mem hxT, fun y hy => ?_, ?_⟩
    · have : y * x⁻¹ * y⁻¹ = (y * x * y⁻¹)⁻¹ := by group
      rw [this, hxc y hy]
    · rw [inv_pow, hx2, inv_one]

theorem i334_unique_involution {T : Subgroup G} (hT : IsPGroup 2 T)
    (hrk : ¬ 1 < pRank 2 (centerOf T)) {Z w : G} (hZT : Z ∈ T) (hwT : w ∈ T)
    (hZc : ∀ x ∈ T, x * Z * x⁻¹ = Z) (hwc : ∀ x ∈ T, x * w * x⁻¹ = w) (hZ1 : Z ≠ 1)
    (hZ2 : Z ^ 2 = 1) (hw2 : w ^ 2 = 1) (hw1 : w ≠ 1) : w = Z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩT : i334Omega T ≤ T := fun x hx => hx.1
  have hΩp : IsPGroup 2 (i334Omega T) := hT.to_le hΩT
  have hΩel : IsElemAbelian 2 (i334Omega T) := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => hx.2.2⟩
    have := b.2.2.1 a a.2.1
    exact mul_inv_eq_iff_eq_mul.1 this
  have hΩc : i334Omega T ≤ centerOf T := by
    intro x hx
    refine Subgroup.mem_map.2 ⟨⟨x, hx.1⟩, Subgroup.mem_center_iff.2 fun g => ?_, rfl⟩
    have := hx.2.1 g g.2
    exact Subtype.ext (mul_inv_eq_iff_eq_mul.1 this)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card.1 hΩp)
  have hkle : k ≤ pRank 2 (centerOf T) := CFSG.SectionRank.le_pRank (by norm_num) hΩc hΩel hk
  have hk1 : k ≤ 1 := hkle.trans (not_lt.1 hrk)
  have hZΩ : Z ∈ i334Omega T := ⟨hZT, hZc, hZ2⟩
  have hwΩ : w ∈ i334Omega T := ⟨hwT, hwc, hw2⟩
  have hk1' : k = 1 := by
    rcases (by omega : k = 0 ∨ k = 1) with h | h
    · exfalso
      subst h
      have h1 : Nat.card (i334Omega T) = 1 := by simpa using hk
      have := (Nat.card_eq_one_iff_unique.1 h1).1
      exact hZ1 (congrArg Subtype.val (Subsingleton.elim (⟨Z, hZΩ⟩ : i334Omega T) 1))
    · exact h
  subst hk1'
  have h2 : Nat.card (i334Omega T) = 2 := by simpa using hk
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : i334Omega T)).1 h2
  have e1 : (⟨w, hwΩ⟩ : i334Omega T) = y := hy _ (fun h => hw1 (congrArg Subtype.val h))
  have e2 : (⟨Z, hZΩ⟩ : i334Omega T) = y := hy _ (fun h => hZ1 (congrArg Subtype.val h))
  exact congrArg Subtype.val (e1.trans e2.symm)

omit [Finite G] in
theorem i334_V_le_U {T U P : Subgroup G} (hU : IsPPlane 2 U) (hUT : U ≤ T) (hPT : P ≤ T)
    {b Z t0 : G} (hb : b ∈ U) (hZ : Z ∈ U)
    (hPmem : ∀ x ∈ T, x ∈ P ↔ x * b * x⁻¹ = b)
    (hPn : ∀ t ∈ T, ∀ p ∈ P, t * p * t⁻¹ ∈ P)
    (hcases : ∀ x ∈ T, x * b * x⁻¹ = b ∨ x * b * x⁻¹ = b * Z)
    (hZc : ∀ x ∈ T, x * Z * x⁻¹ = Z)
    (hΩ : ∀ w ∈ T, (∀ x ∈ T, x * w * x⁻¹ = w) → w ^ 2 = 1 → w = 1 ∨ w = Z)
    (ht0 : t0 ∈ T) (ht0P : t0 ∉ P) {z : G} (hzP : z ∈ P) (hzc : ∀ p ∈ P, p * z * p⁻¹ = z)
    (hz2 : z ^ 2 = 1) : z ∈ U := by
  have hb2 : b ^ 2 = 1 := hU.1.2 b hb
  have hZ2 : Z ^ 2 = 1 := hU.1.2 Z hZ
  have hbT : b ∈ T := hUT hb
  have hZT : Z ∈ T := hUT hZ
  have hzT : z ∈ T := hPT hzP
  have hZinv : Z⁻¹ = Z := i334_inv_eq hU hZ
  have hbinv : b⁻¹ = b := i334_inv_eq hU hb
  have hbZc : b * Z = Z * b := i334_comm hU hb hZ
  have ht0b : t0 * b * t0⁻¹ = b * Z :=
    (hcases t0 ht0).resolve_left (fun h => ht0P ((hPmem t0 ht0).2 h))
  have ht0b' : t0⁻¹ * b * t0 = b * Z := by
    have e : t0⁻¹ * (t0 * b * t0⁻¹) * t0 = b := by group
    rw [ht0b] at e
    have e2 : t0⁻¹ * (b * Z) * t0 = (t0⁻¹ * b * t0) * (t0⁻¹ * Z * t0) := by group
    have e3 : t0⁻¹ * Z * t0 = Z := by simpa using hZc t0⁻¹ (T.inv_mem ht0)
    rw [e2, e3] at e
    rw [← hZinv]
    exact eq_mul_inv_of_mul_eq e
  have hmove : ∀ x ∈ T, x * b * x⁻¹ = b * Z → x * t0 ∈ P ∧ x * t0⁻¹ ∈ P := by
    intro x hx hxb
    have hxZ := hZc x hx
    have key : x * (b * Z) * x⁻¹ = b := by
      have : x * (b * Z) * x⁻¹ = (x * b * x⁻¹) * (x * Z * x⁻¹) := by group
      rw [this, hxb, hxZ, mul_assoc, ← sq, hZ2, mul_one]
    refine ⟨(hPmem _ (T.mul_mem hx ht0)).2 ?_, (hPmem _ (T.mul_mem hx (T.inv_mem ht0))).2 ?_⟩
    · have : x * t0 * b * (x * t0)⁻¹ = x * (t0 * b * t0⁻¹) * x⁻¹ := by group
      rw [this, ht0b, key]
    · have : x * t0⁻¹ * b * (x * t0⁻¹)⁻¹ = x * (t0⁻¹ * b * t0) * x⁻¹ := by group
      rw [this, ht0b', key]
  set z' : G := t0 * z * t0⁻¹ with hz'
  have hz'P : z' ∈ P := hPn t0 ht0 z hzP
  have hz'c : ∀ p ∈ P, p * z' * p⁻¹ = z' := by
    intro p hp
    have hq : t0⁻¹ * p * t0 ∈ P := by
      have := hPn t0⁻¹ (T.inv_mem ht0) p hp
      simpa using this
    have e : p * z' * p⁻¹ = t0 * ((t0⁻¹ * p * t0) * z * (t0⁻¹ * p * t0)⁻¹) * t0⁻¹ := by
      rw [hz']; group
    rw [e, hzc _ hq]
  have hz'2 : z' ^ 2 = 1 := by
    rw [hz', conj_pow, hz2]
    simp
  have hzz' : z * z' = z' * z := by
    have := hzc z' hz'P
    exact (mul_inv_eq_iff_eq_mul.1 this).symm
  have hconj : ∀ x ∈ T, (x * b * x⁻¹ = b ∧ x * z * x⁻¹ = z ∧ x * z' * x⁻¹ = z') ∨
      (x * b * x⁻¹ = b * Z ∧ x * z * x⁻¹ = z' ∧ x * z' * x⁻¹ = z) := by
    intro x hx
    rcases hcases x hx with h | h
    · left
      have hxP := (hPmem x hx).2 h
      exact ⟨h, hzc x hxP, hz'c x hxP⟩
    · right
      obtain ⟨h1, h2⟩ := hmove x hx h
      refine ⟨h, ?_, ?_⟩
      · have e : x * z * x⁻¹ = (x * t0⁻¹) * z' * (x * t0⁻¹)⁻¹ := by
          rw [hz']; group
        rw [e, hz'c _ h2]
      · have e : x * z' * x⁻¹ = (x * t0) * z * (x * t0)⁻¹ := by
          rw [hz']; group
        rw [e, hzc _ h1]
  have hzinv : z⁻¹ = z := by
    rw [inv_eq_iff_mul_eq_one, ← sq, hz2]
  have hwc : ∀ x ∈ T, x * (z * z') * x⁻¹ = z * z' := by
    intro x hx
    have e : x * (z * z') * x⁻¹ = (x * z * x⁻¹) * (x * z' * x⁻¹) := by group
    rcases hconj x hx with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩
    · rw [e, h1, h2]
    · rw [e, h1, h2]
      exact hzz'.symm
  have hw2 : (z * z') ^ 2 = 1 := by
    rw [(show Commute z z' from hzz').mul_pow, hz2, hz'2, one_mul]
  rcases hΩ _ (T.mul_mem hzT (hPT hz'P)) hwc hw2 with hw1 | hwZ
  · have hzz1 : z' = z := by
      rw [eq_inv_of_mul_eq_one_right hw1, hzinv]
    have hcen : ∀ x ∈ T, x * z * x⁻¹ = z := by
      intro x hx
      rcases hconj x hx with ⟨-, h1, -⟩ | ⟨-, h1, -⟩
      · exact h1
      · rw [h1, hzz1]
    rcases hΩ z hzT hcen hz2 with h | h
    · rw [h]
      exact U.one_mem
    · rw [h]
      exact hZ
  · have hz'Z : z' = z * Z := by
      rw [eq_inv_mul_of_mul_eq hwZ, hzinv]
    have hzb : z * b = b * z := by
      have := (hPmem z hzT).1 hzP
      exact mul_inv_eq_iff_eq_mul.1 this
    have hcen : ∀ x ∈ T, x * (z * b) * x⁻¹ = z * b := by
      intro x hx
      have e : x * (z * b) * x⁻¹ = (x * z * x⁻¹) * (x * b * x⁻¹) := by group
      rcases hconj x hx with ⟨h0, h1, -⟩ | ⟨h0, h1, -⟩
      · rw [e, h0, h1]
      · rw [e, h0, h1, hz'Z]
        calc z * Z * (b * Z) = z * (Z * b) * Z := by group
          _ = z * (b * Z) * Z := by rw [← hbZc]
          _ = z * b * (Z * Z) := by group
          _ = z * b := by rw [← sq, hZ2, mul_one]
    have hu2 : (z * b) ^ 2 = 1 := by
      rw [(show Commute z b from hzb).mul_pow, hz2, hb2, one_mul]
    rcases hΩ _ (T.mul_mem hzT hbT) hcen hu2 with h | h
    · have : z = b := by rw [eq_inv_of_mul_eq_one_left h, hbinv]
      rw [this]
      exact hb
    · have : z = Z * b := by
        rw [eq_mul_inv_of_mul_eq h, hbinv]
      rw [this]
      exact U.mul_mem hZ hb

theorem i334_exists_sylow {C P : Subgroup G} (hPC : P ≤ C) (hP : IsPGroup 2 P) :
    ∃ S : Subgroup G, S ≤ C ∧ IsPGroup 2 S ∧ P ≤ S ∧ pCoreOf 2 C ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP' : IsPGroup 2 (P.subgroupOf C) :=
    hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPC).symm
  obtain ⟨S, hS⟩ := hP'.exists_le_sylow
  refine ⟨(S : Subgroup C).map C.subtype, Subgroup.map_subtype_le _, S.isPGroup'.map C.subtype,
    ?_, ?_⟩
  · rw [← Subgroup.map_subgroupOf_eq_of_le hPC]
    exact Subgroup.map_mono hS
  · refine Subgroup.map_mono ?_
    have hN : (CFSG.Open.pCore 2 C).Normal := CFSG.LieType.BorelTits.pCore_normal 2
    exact (CFSG.LieType.BorelTits.pCore_isPGroup (G := C) 2).le_sylow_of_normal S

theorem i334_card_le (T : Sylow 2 G) {S : Subgroup G} (hS : IsPGroup 2 S) :
    Nat.card S ≤ Nat.card (T : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR⟩ := hS.exists_le_sylow
  calc Nat.card S ≤ Nat.card (R : Subgroup G) := Subgroup.card_le_of_le hR
    _ = Nat.card (T : Subgroup G) := by rw [R.card_eq_multiplicity, T.card_eq_multiplicity]

theorem i334_caseB {T U : Subgroup G} (hT2 : IsPGroup 2 T)
    (hmax : ∀ S : Subgroup G, IsPGroup 2 S → Nat.card S ≤ Nat.card T)
    (hU : IsPPlane 2 U) (hUT : U ≤ T) (hTU : ∀ t ∈ T, ∀ x ∈ U, t * x * t⁻¹ ∈ U)
    (hrk : ¬ 1 < pRank 2 (centerOf T)) {b t0 : G} (hb : b ∈ U) (hb1 : b ≠ 1) (ht0 : t0 ∈ T)
    (ht0b : t0 * b * t0⁻¹ ≠ b) :
    pCoreOf 2 (Subgroup.centralizer ({b} : Set G)) ≤ Subgroup.normalizer (U : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hb2 : b ^ 2 = 1 := hU.1.2 b hb
  have hbT : b ∈ T := hUT hb
  have hU1 : U ≠ ⊥ := by
    intro h
    rw [h, Subgroup.mem_bot] at hb
    exact hb1 hb
  obtain ⟨Z, hZU, hZ1, hZc⟩ := i334_exists_central hT2 hTU hUT hU1
  have hZT : Z ∈ T := hUT hZU
  have hZ2 : Z ^ 2 = 1 := hU.1.2 Z hZU
  have hZinv : Z⁻¹ = Z := i334_inv_eq hU hZU
  have hbZ : b ≠ Z := by
    intro h
    apply ht0b
    rw [h]
    exact hZc t0 ht0
  have hcases : ∀ x ∈ T, x * b * x⁻¹ = b ∨ x * b * x⁻¹ = b * Z := by
    intro x hx
    rcases i334_mem_four hU hb hZU hb1 hZ1 hbZ (hTU x hx b hb) with h | h | h | h
    · exfalso
      apply hb1
      simpa using h
    · exact Or.inl h
    · exfalso
      apply hbZ
      calc b = x⁻¹ * (x * b * x⁻¹) * x := by group
        _ = x⁻¹ * Z * x := by rw [h]
        _ = Z := by simpa using hZc x⁻¹ (T.inv_mem hx)
    · exact Or.inr h
  have hΩ : ∀ w ∈ T, (∀ x ∈ T, x * w * x⁻¹ = w) → w ^ 2 = 1 → w = 1 ∨ w = Z := by
    intro w hwT hwc hw2
    by_cases hw1 : w = 1
    · exact Or.inl hw1
    · exact Or.inr (i334_unique_involution hT2 hrk hZT hwT hZc hwc hZ1 hZ2 hw2 hw1)
  set P : Subgroup G := T ⊓ Subgroup.centralizer (U : Set G) with hPdef
  have hPT : P ≤ T := inf_le_left
  have hpc : ∀ p ∈ P, ∀ u ∈ U, p * u * p⁻¹ = u := by
    intro p hp u hu
    rw [mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hp).2 u hu).symm
  have hPmem : ∀ x ∈ T, x ∈ P ↔ x * b * x⁻¹ = b := by
    intro x hx
    constructor
    · intro h
      exact hpc x h b hb
    · intro h
      refine Subgroup.mem_inf.2 ⟨hx, Subgroup.mem_centralizer_iff.2 fun u hu => ?_⟩
      have hxb : ∀ y ∈ U, x * y * x⁻¹ = y → y * x = x * y := by
        intro y _ hy
        exact (mul_inv_eq_iff_eq_mul.1 hy).symm
      refine hxb u hu ?_
      rcases i334_mem_four hU hb hZU hb1 hZ1 hbZ hu with h1 | h1 | h1 | h1
      · rw [h1]
        simp
      · rw [h1, h]
      · rw [h1]
        exact hZc x hx
      · rw [h1]
        have : x * (b * Z) * x⁻¹ = (x * b * x⁻¹) * (x * Z * x⁻¹) := by group
        rw [this, h, hZc x hx]
  have hPn : ∀ t ∈ T, ∀ p ∈ P, t * p * t⁻¹ ∈ P := by
    intro t ht p hp
    refine Subgroup.mem_inf.2 ⟨T.mul_mem (T.mul_mem ht (hPT hp)) (T.inv_mem ht),
      Subgroup.mem_centralizer_iff.2 fun u hu => ?_⟩
    have hu' : t⁻¹ * u * t ∈ U := by simpa using hTU t⁻¹ (T.inv_mem ht) u hu
    have := hpc p hp _ hu'
    have e : t * p * t⁻¹ * u * (t * p * t⁻¹)⁻¹ = t * (p * (t⁻¹ * u * t) * p⁻¹) * t⁻¹ := by group
    have key : t * p * t⁻¹ * u * (t * p * t⁻¹)⁻¹ = u := by
      rw [e, this]
      group
    exact (mul_inv_eq_iff_eq_mul.1 key).symm
  have ht0b' : t0 * b * t0⁻¹ = b * Z := (hcases t0 ht0).resolve_left ht0b
  have ht0P : t0 ∉ P := fun h => ht0b ((hPmem t0 ht0).1 h)
  have hbZb : b * Z ≠ b := fun h => hZ1 (by simpa using h)
  have hidx : (P.subgroupOf T).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨t0, ht0⟩, fun x => ?_⟩
    have hmem : ∀ y : T, y ∈ P.subgroupOf T ↔ (y : G) * b * (y : G)⁻¹ = b := fun y =>
      (Subgroup.mem_subgroupOf).trans (hPmem y y.2)
    have hxt0 : (x : G) * t0 * b * ((x : G) * t0)⁻¹ =
        ((x : G) * b * (x : G)⁻¹) * ((x : G) * Z * (x : G)⁻¹) := by
      have : (x : G) * t0 * b * ((x : G) * t0)⁻¹ = (x : G) * (t0 * b * t0⁻¹) * (x : G)⁻¹ := by
        group
      rw [this, ht0b']
      group
    rcases hcases x x.2 with h | h
    · right
      refine ⟨(hmem x).2 h, fun h' => ?_⟩
      have h2 := (hmem ⟨(x : G) * t0, T.mul_mem x.2 ht0⟩).1 h'
      change (x : G) * t0 * b * ((x : G) * t0)⁻¹ = b at h2
      rw [hxt0, h, hZc _ x.2] at h2
      exact hbZb h2
    · left
      refine ⟨(hmem ⟨(x : G) * t0, T.mul_mem x.2 ht0⟩).2 ?_, fun h' => ?_⟩
      · change (x : G) * t0 * b * ((x : G) * t0)⁻¹ = b
        rw [hxt0, h, hZc _ x.2, mul_assoc, ← sq, hZ2, mul_one]
      · have h2 := (hmem x).1 h'
        rw [h] at h2
        exact hbZb h2
  have hPC : P ≤ Subgroup.centralizer ({b} : Set G) := by
    intro p hp
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact (mul_inv_eq_iff_eq_mul.1 (hpc p hp b hb)).symm
  obtain ⟨S, hSC, hS2, hPS, hQS⟩ := i334_exists_sylow hPC (hT2.to_le hPT)
  have hPcard : Nat.card P * 2 = Nat.card T := by
    have := Subgroup.card_mul_index (P.subgroupOf T)
    rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPT).toEquiv] at this
    exact this
  have hHcard : Nat.card (P.subgroupOf S) = Nat.card P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPS).toEquiv
  have hSidx : (P.subgroupOf S).index ≤ 2 := by
    have h1 := Subgroup.card_mul_index (P.subgroupOf S)
    have h2 := hmax S hS2
    rw [hHcard] at h1
    have hpos : 0 < Nat.card P := Nat.card_pos
    by_contra hcon
    have hcon : 2 < (P.subgroupOf S).index := not_le.1 hcon
    have : Nat.card P * 3 ≤ Nat.card P * (P.subgroupOf S).index :=
      Nat.mul_le_mul_left _ hcon
    omega
  have hN : (P.subgroupOf S).Normal := by
    have hne : (P.subgroupOf S).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    rcases (by omega : (P.subgroupOf S).index = 1 ∨ (P.subgroupOf S).index = 2) with h | h
    · rw [Subgroup.index_eq_one.1 h]
      infer_instance
    · exact Subgroup.normal_of_index_eq_two h
  have hSn : ∀ s ∈ S, ∀ p ∈ P, s * p * s⁻¹ ∈ P := by
    intro s hs p hp
    have := hN.conj_mem ⟨p, hPS hp⟩ (Subgroup.mem_subgroupOf.2 hp) ⟨s, hs⟩
    exact Subgroup.mem_subgroupOf.1 this
  have hUP : U ≤ P := by
    intro u hu
    refine Subgroup.mem_inf.2 ⟨hUT hu, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
    exact i334_comm hU hy hu
  have hSU : ∀ s ∈ S, ∀ u ∈ U, s * u * s⁻¹ ∈ U := by
    intro s hs u hu
    refine i334_V_le_U hU hUT hPT hb hZU hPmem hPn hcases hZc hΩ ht0 ht0P (hSn s hs u (hUP hu))
      ?_ ?_
    · intro p hp
      have hq : s⁻¹ * p * s ∈ P := by simpa using hSn s⁻¹ (S.inv_mem hs) p hp
      have e : p * (s * u * s⁻¹) * p⁻¹ = s * ((s⁻¹ * p * s) * u * (s⁻¹ * p * s)⁻¹) * s⁻¹ := by
        group
      rw [e, hpc _ hq u hu]
    · rw [conj_pow, hU.1.2 u hu]
      simp
  intro q hq
  have hqS := hQS hq
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => hSU q hqS x hx, fun hx => ?_⟩
  have := hSU q⁻¹ (S.inv_mem hqS) _ hx
  simpa [mul_assoc] using this

theorem i334_pCore_le_normalizer {T : Sylow 2 G} {U : Subgroup G}
    (hU : IsUGroup 2 (T : Subgroup G) U) {b : G} (hb : b ∈ U) (hb1 : b ≠ 1) :
    pCoreOf 2 (Subgroup.centralizer ({b} : Set G)) ≤ Subgroup.normalizer (U : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hUT, hTN, hplane, hcen⟩ := hU
  have hT2 : IsPGroup 2 (T : Subgroup G) := T.isPGroup'
  have hTU : ∀ t ∈ (T : Subgroup G), ∀ x ∈ U, t * x * t⁻¹ ∈ U := fun t ht x hx =>
    (Subgroup.mem_normalizer_iff.1 (hTN ht) x).1 hx
  by_cases hTC : (T : Subgroup G) ≤ Subgroup.centralizer ({b} : Set G)
  · obtain ⟨S, -, hS2, hTS, hQS⟩ := i334_exists_sylow hTC hT2
    have hST : S = (T : Subgroup G) := T.is_maximal' hS2 hTS
    intro q hq
    exact hTN (hST ▸ hQS hq)
  · obtain ⟨t0, ht0T, ht0C⟩ := IsConcreteLE.not_le_iff_exists.1 hTC
    have ht0b : t0 * b * t0⁻¹ ≠ b := by
      intro h
      apply ht0C
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact (mul_inv_eq_iff_eq_mul.1 h).symm
    have hrk : ¬ 1 < pRank 2 (centerOf (T : Subgroup G)) := by
      intro h
      obtain ⟨x, hx, hxb⟩ := Subgroup.mem_map.1 (hcen h hb)
      apply ht0b
      have hxb' : (x : G) = b := hxb
      have := congrArg Subtype.val (Subgroup.mem_center_iff.1 hx ⟨t0, ht0T⟩)
      have h2 : t0 * b = b * t0 := by
        rw [← hxb']
        exact this
      rw [h2]
      group
    exact i334_caseB hT2 (fun S hS => i334_card_le T hS) hplane hUT hTU hrk hb hb1 ht0T ht0b

theorem i334_le_pCore_centralizer (hchar : IsCharTwoType G) {T : Sylow 2 G} {U : Subgroup G}
    (hU : IsUGroup 2 (T : Subgroup G) U) {b : G} (hb : b ∈ U) (hb1 : b ≠ 1) :
    U ≤ pCoreOf 2 (Subgroup.centralizer ({b} : Set G)) :=
  i334_le_pCore hchar hU.2.2.1 hb hb1 (i334_pCore_le_normalizer hU hb hb1)

end Sylow



theorem input33_4_proved : CFSG.HardMathSupport.Solomon.UniquenessMaximal.Input33_4 := by
  intro G _ _ hchar T U hU Y hY hUY
  exact i334_centralizes hU.2.2.1 (fun b hb hb1 => i334_le_pCore_centralizer hchar hU hb hb1)
    hY.not_two_dvd_nat hUY

end CFSG.HardMathSupport.Solomon.Coordinator
