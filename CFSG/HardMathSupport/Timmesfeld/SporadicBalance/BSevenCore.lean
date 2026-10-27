module

public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreBasics

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving

variable {G : Type*} [Group G] [Finite G]

private theorem exists_fixedPointFree_conj {N : Subgroup G} {y : G}
    (hyN : ∀ k ∈ N, y * k * y⁻¹ ∈ N) (hy2 : y ^ 2 = 1)
    (hfix : ∀ k ∈ N, k * y = y * k → k = 1) :
    ∃ φ : N →* N, MonoidHom.FixedPointFree φ ∧ Function.Involutive φ ∧
      ∀ k : N, (φ k : G) = y * k * y⁻¹ := by
  refine ⟨{ toFun := fun k => ⟨y * k * y⁻¹, hyN k k.2⟩
            map_one' := by ext; simp
            map_mul' := fun k l => by ext; simp [mul_assoc] }, ?_, ?_, fun k => rfl⟩
  · intro k hk
    have h : y * (k : G) * y⁻¹ = k := congrArg Subtype.val hk
    apply Subtype.ext
    apply hfix k k.2
    calc (k : G) * y = y * k * y⁻¹ * y := by rw [h]
      _ = y * k := by group
  · intro k
    apply Subtype.ext
    change y * (y * (k : G) * y⁻¹) * y⁻¹ = k
    have hy : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by rw [← sq, hy2])
    rw [hy]
    calc y * (y * (k : G) * y) * y = y ^ 2 * k * y ^ 2 := by simp only [sq, mul_assoc]
      _ = k := by rw [hy2, one_mul, mul_one]

private theorem conj_eq_inv_of_inf_centralizer_eq_bot {K : Subgroup G} {y : G}
    (hy2 : y ^ 2 = 1) (hyK : ∀ k ∈ K, y * k * y⁻¹ ∈ K)
    (hyc : K ⊓ Subgroup.centralizer ({y} : Set G) = ⊥) {k : G} (hk : k ∈ K) :
    y * k * y⁻¹ = k⁻¹ := by
  have hfix : ∀ l ∈ K, l * y = y * l → l = 1 := by
    intro l hl hly
    have hmem : l ∈ K ⊓ Subgroup.centralizer ({y} : Set G) :=
      ⟨hl, Subgroup.mem_centralizer_singleton_iff.mpr hly⟩
    rw [hyc] at hmem
    exact Subgroup.mem_bot.mp hmem
  obtain ⟨φ, hφ, hφ2, hφy⟩ := exists_fixedPointFree_conj hyK hy2 hfix
  have h := congrArg Subtype.val (congrFun (hφ.coe_eq_inv_of_involutive hφ2) ⟨k, hk⟩)
  rwa [hφy] at h

set_option linter.unusedVariables false in
theorem eq_bot_of_klein_centralizers {K : Subgroup G} {a b : G}
    (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1) (hab : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hab1 : a ≠ b) (hKa : ∀ k ∈ K, a * k * a⁻¹ ∈ K) (hKb : ∀ k ∈ K, b * k * b⁻¹ ∈ K)
    (hodd : Odd (Nat.card K)) (hKa' : K ⊓ Subgroup.centralizer ({a} : Set G) = ⊥)
    (hKb' : K ⊓ Subgroup.centralizer ({b} : Set G) = ⊥)
    (hKab' : K ⊓ Subgroup.centralizer ({a * b} : Set G) = ⊥) : K = ⊥ := by
  rw [← hKab']
  refine (inf_eq_left.mpr fun k hk => Subgroup.mem_centralizer_singleton_iff.mpr ?_).symm
  have hb' : b * k * b⁻¹ = k⁻¹ := conj_eq_inv_of_inf_centralizer_eq_bot hb2 hKb hKb' hk
  have ha' : a * k⁻¹ * a⁻¹ = k := by
    rw [conj_eq_inv_of_inf_centralizer_eq_bot ha2 hKa hKa' (inv_mem hk), inv_inv]
  calc k * (a * b) = a * (b * k * b⁻¹) * a⁻¹ * (a * b) := by rw [hb', ha']
    _ = a * b * k := by group

private theorem exists_odd_complement {H : Type*} [Group H] [Finite H] {α : H}
    (hα2 : α ^ 2 = 1) (hα1 : α ≠ 1) (hfix : ∀ x : H, x * α = α * x → x = 1 ∨ x = α) :
    ∃ M : Subgroup H, Nat.card M * 2 = Nat.card H ∧ ¬ 2 ∣ Nat.card M ∧
      ∀ x : H, Odd (orderOf x) → x ∈ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hαord : orderOf α = 2 := orderOf_eq_prime hα2 hα1
  have hzp : IsPGroup 2 (Subgroup.zpowers α) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hαord, pow_one])
  obtain ⟨P, hP⟩ := hzp.exists_le_sylow
  have hαP : α ∈ P := hP (Subgroup.mem_zpowers α)
  have hPel : ∀ x ∈ P, x = 1 ∨ x = α := by
    have : Nontrivial P := ⟨⟨1, ⟨α, hαP⟩, fun h => hα1 (congrArg Subtype.val h).symm⟩⟩
    have := P.isPGroup'.center_nontrivial
    obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center P)
    have hzα : ((z : P) : H) = α := by
      have hc := congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨α, hαP⟩)
      rcases hfix _ hc.symm with h | h
      · exact absurd (Subtype.ext (Subtype.ext h)) hz
      · exact h
    intro x hx
    apply hfix
    have hc := congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨x, hx⟩)
    rw [← hzα]
    exact hc
  have hPeq : (P : Subgroup H) = Subgroup.zpowers α := by
    refine le_antisymm (fun x hx => ?_) hP
    rcases hPel x hx with rfl | rfl
    · exact one_mem _
    · exact Subgroup.mem_zpowers _
  have hcardP : Nat.card P = 2 := by
    change Nat.card (P : Subgroup H) = 2
    rw [hPeq, Nat.card_zpowers, hαord]
  have hcyc : IsCyclic P := isCyclic_of_prime_card hcardP
  have hmin : (Nat.card H).minFac = 2 :=
    (Nat.minFac_eq_two_iff _).mpr (hαord ▸ orderOf_dvd_natCard α)
  have hNC := hcyc.normalizer_le_centralizer hmin
  refine ⟨(MonoidHom.transferSylow P hNC).ker, ?_,
    MonoidHom.not_dvd_card_ker_transferSylow P hNC, fun x hx => ?_⟩
  · have h := (hcyc.isComplement' hmin).card_mul_card
    rwa [hcardP] at h
  · rw [MonoidHom.mem_ker]
    apply orderOf_eq_one_iff.mp
    have h1 : orderOf (MonoidHom.transferSylow P hNC x) ∣ orderOf x := orderOf_map_dvd _ x
    have h2 : orderOf (MonoidHom.transferSylow P hNC x) ∣ 2 := by
      have h := orderOf_dvd_natCard (MonoidHom.transferSylow P hNC x)
      rwa [hcardP] at h
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact h
    · exact absurd (even_iff_two_dvd.mpr (h ▸ h1)) (Nat.not_even_iff_odd.mpr hx)

theorem card_le_two_of_normal_core {C N : Subgroup G} (hNC : N ≤ C)
    (hNn : ∀ c ∈ C, ∀ n ∈ N, c * n * c⁻¹ ∈ N)
    (hodd : ∀ K : Subgroup G, K ≤ N → (∀ c ∈ C, ∀ k ∈ K, c * k * c⁻¹ ∈ K) →
      Odd (Nat.card K) → K = ⊥)
    {α : G} (hαC : α ∈ C) (hα2 : α ^ 2 = 1) (hα1 : α ≠ 1)
    (hfix : ∀ n ∈ N, n * α = α * n → n = 1 ∨ n = α) : Nat.card N ≤ 2 := by
  by_cases hαN : α ∈ N
  · set α' : N := ⟨α, hαN⟩
    have hα'2 : α' ^ 2 = 1 := Subtype.ext (by simpa [α'] using hα2)
    have hα'1 : α' ≠ 1 := fun h => hα1 (congrArg Subtype.val h)
    have hfix' : ∀ x : N, x * α' = α' * x → x = 1 ∨ x = α' := by
      intro x hx
      rcases hfix x x.2 (congrArg Subtype.val hx) with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    obtain ⟨M, hMcard, hModd, hMmem⟩ := exists_odd_complement hα'2 hα'1 hfix'
    have hModd' : Odd (Nat.card M) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hModd)
    have hM' : M.map N.subtype = ⊥ := by
      refine hodd _ (Subgroup.map_subtype_le M) (fun c hc m hm => ?_)
        ((Subgroup.card_subtype N M).symm ▸ hModd')
      obtain ⟨m₀, hm₀, rfl⟩ := Subgroup.mem_map.mp hm
      refine Subgroup.mem_map.mpr ⟨⟨c * m₀ * c⁻¹, hNn c hc m₀ m₀.2⟩, hMmem _ ?_, rfl⟩
      have hsc : SemiconjBy c (m₀ : G) (c * m₀ * c⁻¹) := by simp [SemiconjBy, mul_assoc]
      rw [Subgroup.orderOf_mk, ← hsc.orderOf_eq c, Subgroup.orderOf_coe]
      exact Odd.of_dvd_nat hModd' (Subgroup.orderOf_dvd_natCard M hm₀)
    have h1 : Nat.card M = 1 := by rw [← Subgroup.card_subtype N M, hM', Subgroup.card_bot]
    rw [← hMcard, h1]
  · have hfix' : ∀ k ∈ N, k * α = α * k → k = 1 := fun k hk hkα =>
      (hfix k hk hkα).resolve_right fun h => hαN (h ▸ hk)
    obtain ⟨φ, hφ, hφ2, -⟩ := exists_fixedPointFree_conj (hNn α hαC) hα2 hfix'
    rw [hodd N le_rfl hNn (hφ.odd_card_of_involutive hφ2), Subgroup.card_bot]
    norm_num

theorem card_gLAPPrimeCoreOf_le_two {p : ℕ} (hp : p.Prime) {C : Subgroup G} {a b α : G}
    (haC : a ∈ C) (hbC : b ∈ C) (hαC : α ∈ C) (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1)
    (hab : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab1 : a ≠ b) (hα2 : α ^ 2 = 1)
    (hα1 : α ≠ 1)
    (hV : ∀ v ∈ ({a, b, a * b} : Set G), ∀ K : Subgroup G,
      K ≤ C ⊓ Subgroup.centralizer ({v} : Set G) → Odd (Nat.card K) → ¬ p ∣ Nat.card K →
      (∀ g ∈ C ⊓ Subgroup.centralizer ({v} : Set G), ∀ k ∈ K, g * k * g⁻¹ ∈ K) → K = ⊥)
    (hα : ∀ K : Subgroup G, K ≤ C ⊓ Subgroup.centralizer ({α} : Set G) → ¬ p ∣ Nat.card K →
      (∀ g ∈ C ⊓ Subgroup.centralizer ({α} : Set G), ∀ k ∈ K, g * k * g⁻¹ ∈ K) →
      ∀ k ∈ K, k = 1 ∨ k = α) :
    Nat.card (GLAPPrimeCoreOf p C) ≤ 2 := by
  have hNC : GLAPPrimeCoreOf p C ≤ C := GLAPPrimeCoreOf_le C
  have hNn : ∀ c ∈ C, ∀ n ∈ GLAPPrimeCoreOf p C, c * n * c⁻¹ ∈ GLAPPrimeCoreOf p C :=
    GLAPPrimeCoreOf_conj_mem
  have hp' : ∀ K : Subgroup G, K ≤ GLAPPrimeCoreOf p C → ¬ p ∣ Nat.card K := fun K hK =>
    (Nat.Prime.coprime_iff_not_dvd hp).mp
      (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hK)
        (coprime_card_GLAPPrimeCoreOf hp C))
  have hcent : ∀ (v : G) (K : Subgroup G), (∀ c ∈ C, ∀ k ∈ K, c * k * c⁻¹ ∈ K) →
      ∀ g ∈ C ⊓ Subgroup.centralizer ({v} : Set G),
        ∀ k ∈ K ⊓ Subgroup.centralizer ({v} : Set G),
          g * k * g⁻¹ ∈ K ⊓ Subgroup.centralizer ({v} : Set G) := fun v K hK g hg k hk =>
    ⟨hK g hg.1 k hk.1, Subgroup.mul_mem _ (Subgroup.mul_mem _ hg.2 hk.2) (Subgroup.inv_mem _ hg.2)⟩
  refine card_le_two_of_normal_core hNC hNn (fun K hKN hKC hKodd => ?_) hαC hα2 hα1
    (fun n hn hnα => ?_)
  · have hloc : ∀ v ∈ ({a, b, a * b} : Set G), K ⊓ Subgroup.centralizer ({v} : Set G) = ⊥ :=
      fun v hv => hV v hv _ (inf_le_inf_right _ (hKN.trans hNC))
        (Odd.of_dvd_nat hKodd (Subgroup.card_dvd_of_le inf_le_left))
        (hp' _ (inf_le_left.trans hKN)) (hcent v K hKC)
    exact eq_bot_of_klein_centralizers ha2 hb2 hab ha1 hb1 hab1 (hKC a haC) (hKC b hbC) hKodd
      (hloc a (by simp)) (hloc b (by simp)) (hloc (a * b) (by simp))
  · exact hα _ (inf_le_inf_right _ hNC) (hp' _ inf_le_left) (hcent α _ hNn) n
      ⟨hn, Subgroup.mem_centralizer_singleton_iff.mpr hnα⟩

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven
