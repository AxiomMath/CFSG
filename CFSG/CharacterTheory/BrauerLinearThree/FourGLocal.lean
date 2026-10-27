module

public import CFSG.CharacterTheory.BrauerLinearThree.NineCharacter

public section

namespace CFSG.BrauerLinearThree

open Matrix CFSG.DesarguesianPlanes

variable {G : Type} [Group G] {F : Type} [Field F] [Finite F] {Z : Subgroup (GL (Fin 2) F)}
  [Z.Normal] {J : G} (φ : Subgroup.centralizer ({J} : Set G) ≃* GL (Fin 2) F ⧸ Z)
  (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F) (hZodd : Odd (Nat.card Z))
  (h2 : (2 : F) ≠ 0) (hJ : orderOf J = 2)

omit [Finite F] in
theorem exists_diagGL_of_commute_diag {a b : Fˣ} (hab : a ≠ b) (A : GL (Fin 2) F)
    (hA : A * diagGL a b = diagGL a b * A) : ∃ c d : Fˣ, A = diagGL c d := by
  have hab' : (a : F) - b ≠ 0 := sub_ne_zero.mpr (fun h => hab (Units.ext h))
  have h01 : (A : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
    have := congrArg (fun M : GL (Fin 2) F => (M : Matrix (Fin 2) (Fin 2) F) 0 1) hA
    simp [diagGL, Matrix.mul_apply, Fin.sum_univ_two] at this
    have h : ((a : F) - b) * (A : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
      linear_combination -this
    exact (mul_eq_zero.mp h).resolve_left hab'
  have h10 : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    have := congrArg (fun M : GL (Fin 2) F => (M : Matrix (Fin 2) (Fin 2) F) 1 0) hA
    simp [diagGL, Matrix.mul_apply, Fin.sum_univ_two] at this
    have h : ((a : F) - b) * (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
      linear_combination this
    exact (mul_eq_zero.mp h).resolve_left hab'
  have hdet : (A : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    have := A.isUnit.map Matrix.detMonoidHom
    exact this.ne_zero
  rw [det_fin_two, h01, h10, mul_zero, sub_zero] at hdet
  have h00 : (A : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := left_ne_zero_of_mul hdet
  have h11 : (A : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := right_ne_zero_of_mul hdet
  refine ⟨Units.mk0 _ h00, Units.mk0 _ h11, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagGL, h01, h10]

omit [Finite F] in
include hZ hZodd h2 in
theorem mem_centralizer_fourV_of_commute_diag {a b : Fˣ} (hab : a ≠ b) {x : G}
    (hxJ : J * x = x * J)
    (hx : x * linearCentralizerHom φ (diagGL a b) = linearCentralizerHom φ (diagGL a b) * x) :
    x ∈ Subgroup.centralizer (fourV φ : Set G) := by
  obtain ⟨A, rfl⟩ := exists_linearCentralizerHom_eq φ hxJ
  have hA := commute_of_linearCentralizerHom_commute φ hZ hZodd h2 hx
  obtain ⟨c, d, rfl⟩ := exists_diagGL_of_commute_diag hab A hA
  exact (mem_centralizer_fourV φ).mpr (isTorus_diag φ c d)

omit [Finite F] in
theorem centralizer_J_le_centralizer_of_mem_centerSub {z : G} (hzC : z ∈ centerSub φ) :
    Subgroup.centralizer ({J} : Set G) ≤ Subgroup.centralizer ({z} : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
  exact (commute_of_mem_centerSub φ hzC hx.symm).symm

omit [Finite F] in
theorem mem_centralizer_fourV_of_mem_centerSub {z : G} (hzC : z ∈ centerSub φ) :
    z ∈ Subgroup.centralizer (fourV φ : Set G) := by
  rw [mem_centralizer_fourV]
  exact ⟨(commute_of_mem_centerSub φ hzC rfl).symm,
    (commute_of_mem_centerSub φ hzC (J_commute_invJ₁ φ)).symm⟩

include hZ hZodd h2 hJ in
theorem mem_centralizer_fourV_of_not_conj [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {z : G} (hzC : z ∈ centerSub φ)
    (hcase : ∀ g ∈ Subgroup.centralizer ({z} : Set G), g * J * g⁻¹ ≠ invJ₁ φ)
    {x : G} (hxz : x ∈ Subgroup.centralizer ({z} : Set G))
    (hx₁ : x * invJ₁ φ = invJ₁ φ * x) :
    x ∈ Subgroup.centralizer (fourV φ : Set G) := by
  have : Finite (Subgroup.centralizer ({J} : Set G)) := Finite.of_equiv _ φ.symm.toEquiv
  obtain ⟨Y, hY₁, hY₂⟩ := exists_Y φ hZ hZodd h2 hJ hnonab
  have hYN := inv_mem_normalizer_fourV φ hZ hZodd h2 hJ hY₁ hY₂
  have hzD := mem_centralizer_fourV_of_mem_centerSub φ hzC
  have hz'D : Y * z * Y⁻¹ ∈ Subgroup.centralizer (fourV φ : Set G) := by
    have h := inv_mul_mul_mem_centralizer_fourV φ hYN hzD
    rwa [inv_inv] at h
  obtain ⟨a, b, hab⟩ := (mem_centralizer_fourV_iff φ hZ hZodd h2).mp hz'D
  obtain ⟨SC⟩ : Nonempty (Sylow 2 (Subgroup.centralizer ({J} : Set G))) := inferInstance
  obtain ⟨S, hS⟩ := exists_sylow_eq_of_sylow_centralizer φ hZ hZodd h2 hJ _ SC rfl
  have hSC : (S : Subgroup G) ≤ Subgroup.centralizer {J} := by
    rw [hS]
    exact Subgroup.map_subtype_le _
  have hSN := normalizer_sylow_le_centralizer φ hZ hZodd h2 hJ S hSC
  have hab' : a ≠ b := by
    rintro rfl
    have hz'C : Y * z * Y⁻¹ ∈ centerSub φ := by
      rw [mem_centerSub]
      refine ⟨a, ?_⟩
      rw [hab]
      congr 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [diagGL, Matrix.GeneralLinearGroup.scalar]
    have h4E := eq_of_conj_mem_centerSub φ S hSC hSN hzC Y⁻¹ (by rwa [inv_inv])
    rw [inv_inv] at h4E
    have hYz : Y⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc Y⁻¹ * z = Y⁻¹ * (Y * z * Y⁻¹) := by rw [h4E]
        _ = z * Y⁻¹ := by group
    apply hcase Y⁻¹ hYz
    rw [inv_inv]
    exact hY₁
  have hx'J : J * (Y * x * Y⁻¹) = (Y * x * Y⁻¹) * J := by
    have hJ' : J = Y * invJ₁ φ * Y⁻¹ := (conj_eq_of_inv_conj_eq hY₁).symm
    rw [hJ']
    calc Y * invJ₁ φ * Y⁻¹ * (Y * x * Y⁻¹) = Y * (invJ₁ φ * x) * Y⁻¹ := by group
      _ = Y * (x * invJ₁ φ) * Y⁻¹ := by rw [hx₁]
      _ = Y * x * Y⁻¹ * (Y * invJ₁ φ * Y⁻¹) := by group
  have hxz' := Subgroup.mem_centralizer_singleton_iff.mp hxz
  have hx'z' : (Y * x * Y⁻¹) * linearCentralizerHom φ (diagGL a b) =
      linearCentralizerHom φ (diagGL a b) * (Y * x * Y⁻¹) := by
    rw [← hab]
    calc Y * x * Y⁻¹ * (Y * z * Y⁻¹) = Y * (x * z) * Y⁻¹ := by group
      _ = Y * (z * x) * Y⁻¹ := by rw [hxz']
      _ = Y * z * Y⁻¹ * (Y * x * Y⁻¹) := by group
  have hx'D := mem_centralizer_fourV_of_commute_diag φ hZ hZodd h2 hab' hx'J hx'z'
  have hYN' : Y ∈ Subgroup.normalizer (fourV φ : Set G) := by
    simpa using (Subgroup.normalizer _).inv_mem hYN
  have h := inv_mul_mul_mem_centralizer_fourV φ hYN' hx'D
  rwa [show Y⁻¹ * (Y * x * Y⁻¹) * Y = x by group] at h

omit [Finite F] in
theorem odd_card_oddCore {H : Type*} [Group H] [Finite H] : Odd (Nat.card (CFSG.oddCore H)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : CFSG.oddCore H ≤ CFSG.pPrimeCore 2 H :=
    sSup_le fun N hN => le_sSup ⟨hN.1, Nat.coprime_two_left.mpr hN.2⟩
  have hdvd : Nat.card (CFSG.oddCore H) ∣ Nat.card (CFSG.pPrimeCore 2 H) :=
    Subgroup.card_dvd_of_le hle
  exact Nat.coprime_two_left.mp
    (Nat.Coprime.of_dvd_right hdvd (CFSG.pPrimeCore_coprime_card (p := 2) (G := H)))

include hZ hZodd h2 hJ in
theorem centralizer_le_of_not_conj [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hq : Nat.card F % 4 = 3) {z : G}
    (hzC : z ∈ centerSub φ)
    (hcase : ∀ g ∈ Subgroup.centralizer ({z} : Set G), g * J * g⁻¹ ≠ invJ₁ φ) :
    Subgroup.centralizer ({z} : Set G) ≤ Subgroup.centralizer {J} := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (Subgroup.centralizer ({J} : Set G)) := Finite.of_equiv _ φ.symm.toEquiv
  have hq3 : 3 ≤ Nat.card F := by
    have := odd_card_F h2
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    omega
  set G₀ := Subgroup.centralizer ({z} : Set G) with hG₀
  have hCG₀ := centralizer_J_le_centralizer_of_mem_centerSub φ hzC
  have hJC : J ∈ Subgroup.centralizer ({J} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  obtain ⟨SC⟩ : Nonempty (Sylow 2 (Subgroup.centralizer ({J} : Set G))) := inferInstance
  obtain ⟨S, hS⟩ := exists_sylow_eq_of_sylow_centralizer φ hZ hZodd h2 hJ _ SC rfl
  have hSC : (S : Subgroup G) ≤ Subgroup.centralizer {J} := by
    rw [hS]
    exact Subgroup.map_subtype_le _
  have hJS : J ∈ (S : Subgroup G) := by
    rw [hS]
    exact ⟨_, (sylow_center_involution φ hZ hZodd h2 hJ SC).1, rfl⟩
  set S₀ : Sylow 2 G₀ := S.subtype (hSC.trans hCG₀)
  have hmemS₀ : ∀ y : G₀, y ∈ (S₀ : Subgroup G₀) ↔ (y : G) ∈ (S : Subgroup G) := by
    intro y
    change y ∈ ((S.subtype (hSC.trans hCG₀) : Sylow 2 G₀) : Subgroup G₀) ↔ _
    rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf]
  set J₀ : G₀ := ⟨J, hCG₀ hJC⟩
  set z₀ : (S₀ : Subgroup G₀) := ⟨J₀, (hmemS₀ J₀).mpr hJS⟩
  have hzZ : z₀ ∈ Subgroup.center (S₀ : Subgroup G₀) := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    apply Subtype.ext
    have hy := Subgroup.mem_centralizer_singleton_iff.mp (hSC ((hmemS₀ _).mp y.2))
    exact hy
  have hz₀ : orderOf z₀ = 2 := by
    have e1 : orderOf z₀ = orderOf ((z₀ : (S₀ : Subgroup G₀)) : G₀) :=
      (Subgroup.orderOf_coe z₀).symm
    have e2 : orderOf J₀ = orderOf J := Subgroup.orderOf_mk J _
    rw [e1]
    exact e2.trans hJ
  have hwc : ∀ g : G₀, g⁻¹ * ((z₀ : (S₀ : Subgroup G₀)) : G₀) * g ∈ (S₀ : Subgroup G₀) →
      g⁻¹ * ((z₀ : (S₀ : Subgroup G₀)) : G₀) * g = z₀ := by
    intro g hg
    rw [hmemS₀] at hg
    have hg' : (g : G)⁻¹ * J * g ∈ (S : Subgroup G) := hg
    apply Subtype.ext
    change (g : G)⁻¹ * J * g = J
    by_contra hne
    have hxJ : J * ((g : G)⁻¹ * J * g) = ((g : G)⁻¹ * J * g) * J :=
      (Subgroup.mem_centralizer_singleton_iff.mp (hSC hg')).symm
    have hx2 : ((g : G)⁻¹ * J * g) * ((g : G)⁻¹ * J * g) = 1 := by
      calc ((g : G)⁻¹ * J * g) * ((g : G)⁻¹ * J * g) = (g : G)⁻¹ * (J * J) * g := by group
        _ = 1 := by rw [J_mul_self hJ]; group
    have hx1 : (g : G)⁻¹ * J * g ≠ 1 := by
      intro h
      have : J = 1 := by
        calc J = (g : G) * ((g : G)⁻¹ * J * g) * (g : G)⁻¹ := by group
          _ = 1 := by rw [h]; group
      rw [this, orderOf_one] at hJ
      exact absurd hJ (by norm_num)
    obtain ⟨h, hhJ, hhx⟩ := exists_conj_invJ₁ φ hZ hZodd h2 hJ hxJ hx2 hx1 hne
    have hhG₀ : h⁻¹ * (g : G)⁻¹ ∈ G₀ := by
      refine G₀.mul_mem (G₀.inv_mem (hCG₀ ?_)) (G₀.inv_mem g.2)
      exact Subgroup.mem_centralizer_singleton_iff.mpr hhJ.symm
    apply hcase _ hhG₀
    calc h⁻¹ * (g : G)⁻¹ * J * (h⁻¹ * (g : G)⁻¹)⁻¹ = h⁻¹ * ((g : G)⁻¹ * J * g) * h := by group
      _ = h⁻¹ * (h * invJ₁ φ * h⁻¹) * h := by rw [hhx]
      _ = invJ₁ φ := by group
  obtain ⟨hfac, -⟩ := CFSG.Adapters.glauberman_zStar S₀ z₀ hzZ hz₀ hwc
  set M : Subgroup G := (CFSG.oddCore G₀).map G₀.subtype with hM
  have hMG₀ : M ≤ G₀ := Subgroup.map_subtype_le _
  have hModd : Odd (Nat.card M) := by
    rw [hM, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    exact odd_card_oddCore
  have hMconj : ∀ g ∈ G₀, ∀ m ∈ M, g * m * g⁻¹ ∈ M := by
    rintro g hg _ ⟨k, hk, rfl⟩
    refine ⟨⟨g, hg⟩ * k * ⟨g, hg⟩⁻¹, (inferInstance : (CFSG.oddCore G₀).Normal).conj_mem k hk _,
      rfl⟩
  have hJ₁G₀ : invJ₁ φ ∈ G₀ := hCG₀ (Subgroup.mem_centralizer_singleton_iff.mpr
    (J_commute_invJ₁ φ).symm)
  have hJG₀ : J ∈ G₀ := hCG₀ hJC
  have hWG₀ : swapW φ ∈ G₀ := hCG₀ (Subgroup.mem_centralizer_singleton_iff.mpr
    (linearCentralizerHom_commute φ swapGL).symm)
  have hiden := card_mul_card_sq_eq_of_four hJ (orderOf_invJ₁ φ hZ h2) (J_commute_invJ₁ φ)
    (J_ne_invJ₁ φ hZ h2) M hModd (fun m hm => hMconj J hJG₀ m hm)
    (fun m hm => hMconj _ hJ₁G₀ m hm)
  set MV := (M ⊓ Subgroup.centralizer {J} ⊓ Subgroup.centralizer {invJ₁ φ} : Subgroup G)
  have hMVD : ∀ x ∈ M, x ∈ Subgroup.centralizer (fourV φ : Set G) → x ∈ MV := by
    intro x hxM hxD
    obtain ⟨h1, h2'⟩ := (mem_centralizer_fourV φ).mp hxD
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hxM,
      Subgroup.mem_centralizer_singleton_iff.mpr h1.symm⟩,
      Subgroup.mem_centralizer_singleton_iff.mpr h2'.symm⟩
  have hle0 : (M ⊓ Subgroup.centralizer {J} : Subgroup G) ≤ MV := by
    intro x hx
    obtain ⟨hxM, hxJ⟩ := Subgroup.mem_inf.mp hx
    set K : Subgroup (Subgroup.centralizer ({J} : Set G)) :=
      (M ⊓ Subgroup.centralizer {J}).subgroupOf (Subgroup.centralizer ({J} : Set G))
    have hKn : K.Normal := by
      constructor
      intro k hk c
      rw [Subgroup.mem_subgroupOf] at hk ⊢
      obtain ⟨hkM, hkJ⟩ := Subgroup.mem_inf.mp hk
      refine Subgroup.mem_inf.mpr ⟨hMconj _ (hCG₀ c.2) _ hkM, ?_⟩
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ c.2 hkJ) (Subgroup.inv_mem _ c.2)
    have hKodd : Odd (Nat.card K) := by
      have hcard : Nat.card K = Nat.card (M ⊓ Subgroup.centralizer {J} : Subgroup G) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
      rw [hcard]
      exact hModd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
    have hxZ := mem_centerSub_of_mem_normal_odd φ hZ hZodd h2 hq3 K hKn hKodd
      (k := ⟨x, hxJ⟩) (by rw [Subgroup.mem_subgroupOf]; exact hx)
    exact hMVD x hxM (mem_centralizer_fourV_of_mem_centerSub φ hxZ)
  have hle1 : (M ⊓ Subgroup.centralizer {invJ₁ φ} : Subgroup G) ≤ MV := by
    intro x hx
    obtain ⟨hxM, hx₁⟩ := Subgroup.mem_inf.mp hx
    exact hMVD x hxM (mem_centralizer_fourV_of_not_conj φ hZ hZodd h2 hJ hnonab hzC hcase
      (hMG₀ hxM) (Subgroup.mem_centralizer_singleton_iff.mp hx₁))
  have hle2 : (M ⊓ Subgroup.centralizer {J * invJ₁ φ} : Subgroup G) ≤ MV := by
    intro x hx
    obtain ⟨hxM, hx₂⟩ := Subgroup.mem_inf.mp hx
    have hx₂' := Subgroup.mem_centralizer_singleton_iff.mp hx₂
    rw [← invJ₂_eq φ hZ hZodd h2 hJ] at hx₂'
    have hW₂ : swapW φ * invJ₂ φ * (swapW φ)⁻¹ = invJ₁ φ := by
      rw [← swapW_conj_invJ₁ φ, swapW_inv]
      calc swapW φ * (swapW φ * invJ₁ φ * swapW φ) * swapW φ =
          (swapW φ * swapW φ) * invJ₁ φ * (swapW φ * swapW φ) := by group
        _ = invJ₁ φ := by rw [swapW_mul_self]; group
    have hyM := hMconj _ hWG₀ x hxM
    have hy₁ : swapW φ * x * (swapW φ)⁻¹ * invJ₁ φ =
        invJ₁ φ * (swapW φ * x * (swapW φ)⁻¹) := by
      rw [← hW₂]
      calc swapW φ * x * (swapW φ)⁻¹ * (swapW φ * invJ₂ φ * (swapW φ)⁻¹) =
          swapW φ * (x * invJ₂ φ) * (swapW φ)⁻¹ := by group
        _ = swapW φ * (invJ₂ φ * x) * (swapW φ)⁻¹ := by rw [hx₂']
        _ = swapW φ * invJ₂ φ * (swapW φ)⁻¹ * (swapW φ * x * (swapW φ)⁻¹) := by group
    have hyD := mem_centralizer_fourV_of_not_conj φ hZ hZodd h2 hJ hnonab hzC hcase
      (hMG₀ hyM) hy₁
    have hxD := inv_mul_mul_mem_centralizer_fourV φ
      (swapW_mem_normalizer_fourV φ hZ hZodd h2 hJ) hyD
    rw [show (swapW φ)⁻¹ * (swapW φ * x * (swapW φ)⁻¹) * swapW φ = x by group] at hxD
    exact hMVD x hxM hxD
  have hc0 := Subgroup.card_le_of_le hle0
  have hc1 := Subgroup.card_le_of_le hle1
  have hc2 := Subgroup.card_le_of_le hle2
  have hMV : MV = M := by
    have hpos : 0 < Nat.card MV := Nat.card_pos
    have hle : Nat.card M * Nat.card MV ^ 2 ≤ Nat.card MV * Nat.card MV * Nat.card MV := by
      rw [hiden]
      exact Nat.mul_le_mul (Nat.mul_le_mul hc0 hc1) hc2
    have hMle : Nat.card M ≤ Nat.card MV := by
      have h3 : Nat.card M * Nat.card MV ^ 2 ≤ Nat.card MV * Nat.card MV ^ 2 := by
        calc Nat.card M * Nat.card MV ^ 2 ≤ Nat.card MV * Nat.card MV * Nat.card MV := hle
          _ = Nat.card MV * Nat.card MV ^ 2 := by ring
      exact Nat.le_of_mul_le_mul_right h3 (by positivity)
    exact Subgroup.eq_of_le_of_card_ge (inf_le_left.trans inf_le_left) hMle
  intro g hg
  obtain ⟨c, hc, k, hk, hgck⟩ := hfac ⟨g, hg⟩
  have hcJ : (c : G) ∈ Subgroup.centralizer ({J} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
    exact congrArg Subtype.val hc
  have hkM : (k : G) ∈ M := ⟨k, hk, rfl⟩
  have hkJ : (k : G) ∈ Subgroup.centralizer ({J} : Set G) := by
    rw [← hMV] at hkM
    exact (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hkM).1).2
  have hg' : g = (c : G) * k := congrArg Subtype.val hgck
  rw [hg']
  exact Subgroup.mul_mem _ hcJ hkJ

end CFSG.BrauerLinearThree
