module

public import CFSG.Open.GLBDefs

public section

namespace CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs

variable {G : Type*} [Group G]

theorem mem_of_pow_three_eq_one_of_index_two {L : Subgroup G} (K : Subgroup L)
    (hK : K.index = 2) {y : G} (hyL : y ∈ L) (hy : y ^ 3 = 1) : (⟨y, hyL⟩ : L) ∈ K := by
  have : K.Normal := Subgroup.normal_of_index_eq_two hK
  have hg : (⟨y, hyL⟩ : L) ^ 3 = 1 := Subtype.ext (by simpa using hy)
  have h2 : (⟨y, hyL⟩ : L) ^ 2 ∈ K := by
    have := Subgroup.pow_index_mem K (⟨y, hyL⟩ : L)
    rwa [hK] at this
  have h4' : (⟨y, hyL⟩ : L) ^ 4 = ⟨y, hyL⟩ := by
    rw [show (4 : ℕ) = 1 + 3 from rfl, pow_add, pow_one, hg, mul_one]
  have h4 : (⟨y, hyL⟩ : L) = ((⟨y, hyL⟩ : L) ^ 2) ^ 2 := by
    rw [← pow_mul, show 2 * 2 = 4 from rfl, h4']
  rw [h4]
  exact pow_mem h2 2

theorem glbPrimeCore_conj_mem {p : ℕ} {M : Subgroup G} {k : G} (hk : k ∈ M) {h : G}
    (hh : h ∈ CFSG.Open.GLBPrimeCore p M) : k * h * k⁻¹ ∈ CFSG.Open.GLBPrimeCore p M := by
  let f : G →* G := (MulAut.conj k).toMonoidHom
  have hf : Function.Injective f := (MulAut.conj k).injective
  have key : CFSG.Open.GLBPrimeCore p M ≤ (CFSG.Open.GLBPrimeCore p M).comap f := by
    apply sSup_le
    intro N hN
    obtain ⟨hNM, hNn, hNp⟩ := hN
    intro n hn
    rw [Subgroup.mem_comap]
    have hmapM : N.map f ≤ M := by
      rintro _ ⟨n', hn', rfl⟩
      show k * n' * k⁻¹ ∈ M
      exact mul_mem (mul_mem hk (hNM hn')) (inv_mem hk)
    have hmapn : ((N.map f).subgroupOf M).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hmapM]
      rintro _ m ⟨n', hn', rfl⟩ hm
      have ht : k⁻¹ * m * k ∈ M := mul_mem (mul_mem (inv_mem hk) hm) hk
      have hnn := (Subgroup.normal_subgroupOf_iff hNM).1 hNn n' (k⁻¹ * m * k) hn' ht
      refine ⟨_, hnn, ?_⟩
      show k * ((k⁻¹ * m * k) * n' * (k⁻¹ * m * k)⁻¹) * k⁻¹ = m * (k * n' * k⁻¹) * m⁻¹
      group
    have hmapp : Nat.Coprime p (Nat.card (N.map f)) := by
      rw [Subgroup.card_map_of_injective hf]
      exact hNp
    have hmem : N.map f ∈ {N : Subgroup G | N ≤ M ∧ (N.subgroupOf M).Normal ∧
        Nat.Coprime p (Nat.card N)} := ⟨hmapM, hmapn, hmapp⟩
    exact le_sSup hmem (Subgroup.mem_map_of_mem f hn)
  exact key hh

theorem le_glbPrimeCore_of {p : ℕ} {H N : Subgroup G} (hNH : N ≤ H)
    (hN : (N.subgroupOf H).Normal) (hp : Nat.Coprime p (Nat.card N)) :
    N ≤ CFSG.Open.GLBPrimeCore p H := by
  apply le_sSup
  exact ⟨hNH, hN, hp⟩

theorem exists_normal_order_three_of_index_six
    {G : Type*} [Group G] [Finite G] {M C L : Subgroup G} (hCL : C ≤ L) (hLM : L ≤ M)
    (hLn : (L.subgroupOf M).Normal) (hCn : (C.subgroupOf M).Normal) (hC3 : ¬ 3 ∣ Nat.card C)
    (hidx : Nat.card L = 6 * Nat.card C) :
    ∃ P₀ : Subgroup G, P₀ ≤ L ∧ Nat.card P₀ = 3 ∧
      ((P₀ ⊔ CFSG.Open.GLBPrimeCore 3 M).subgroupOf M).Normal := by
  classical
  have hCM : C ≤ M := hCL.trans hLM
  have hcop : Nat.Coprime 3 (Nat.card C) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hC3
  have hcpos : 0 < Nat.card C := Nat.card_pos
  have h3L : 3 ∣ Nat.card L := ⟨2 * Nat.card C, by rw [hidx]; ring⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 (hp := ⟨Nat.prime_three⟩) h3L
  have hxG : orderOf (x : G) = 3 := by rw [Subgroup.orderOf_coe, hx]
  have hx3 : (x : G) ^ 3 = 1 := by rw [← hxG]; exact pow_orderOf_eq_one _
  obtain ⟨P₀, hP₀def⟩ : ∃ P : Subgroup G, P = Subgroup.zpowers (x : G) := ⟨_, rfl⟩
  have hP₀L : P₀ ≤ L := by
    rw [hP₀def]; exact Subgroup.zpowers_le.2 x.2
  have hP₀M : P₀ ≤ M := hP₀L.trans hLM
  have hP₀card : Nat.card P₀ = 3 := by rw [hP₀def, Nat.card_zpowers, hxG]
  have hCLn : (C.subgroupOf L).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hCL]
    intro h k hh hk
    exact (Subgroup.normal_subgroupOf_iff hCM).1 hCn h k hh (hLM hk)
  obtain ⟨A', hA'def⟩ : ∃ A : Subgroup L, A = Subgroup.zpowers x := ⟨_, rfl⟩
  have hA'card : Nat.card A' = 3 := by rw [hA'def, Nat.card_zpowers, hx]
  have hC'card : Nat.card (C.subgroupOf L) = Nat.card C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCL).toEquiv
  have hcop' : Nat.Coprime (Nat.card (C.subgroupOf L)) (Nat.card A') := by
    rw [hC'card, hA'card]; exact hcop.symm
  have hinf : (C.subgroupOf L) ⊓ A' = ⊥ := disjoint_iff.1 (Subgroup.disjoint_of_coprime_natCard hcop')
  have rel1 : (C.subgroupOf L).relIndex A' = 3 := by
    have h := Subgroup.relIndex_mul_card (H := C.subgroupOf L) (K := A')
    rw [hinf, Subgroup.card_bot, mul_one, hA'card] at h
    exact h
  have : (C.subgroupOf L).Normal := hCLn
  have rel2 : (C.subgroupOf L).relIndex (A' ⊔ C.subgroupOf L) = (C.subgroupOf L).relIndex A' :=
    Subgroup.relIndex_sup_right A' (C.subgroupOf L)
  have cardK : Nat.card ↥(A' ⊔ C.subgroupOf L) = 3 * Nat.card C := by
    have h := Subgroup.relIndex_mul_card (H := C.subgroupOf L) (K := A' ⊔ C.subgroupOf L)
    rw [inf_eq_left.2 (le_sup_right : C.subgroupOf L ≤ A' ⊔ C.subgroupOf L), hC'card, rel2,
      rel1] at h
    exact h.symm
  have hindex : (A' ⊔ C.subgroupOf L).index = 2 := by
    have h := Subgroup.index_mul_card (H := A' ⊔ C.subgroupOf L)
    rw [cardK, hidx] at h
    have h' : (A' ⊔ C.subgroupOf L).index * (3 * Nat.card C) = 2 * (3 * Nat.card C) := by
      rw [h]; ring
    exact Nat.eq_of_mul_eq_mul_right (by omega) h'
  have hK'G : ∀ g ∈ A' ⊔ C.subgroupOf L, (g : G) ∈ P₀ ⊔ C := by
    have hle : A' ⊔ C.subgroupOf L ≤ (P₀ ⊔ C).comap L.subtype := by
      apply sup_le
      · rw [hA'def]
        apply Subgroup.zpowers_le.2
        rw [Subgroup.mem_comap, hP₀def]
        exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
      · intro c hc
        rw [Subgroup.mem_comap]
        exact Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.1 hc)
    intro g hg
    exact hle hg
  have key : ∀ y : G, ∀ hyL : y ∈ L, y ^ 3 = 1 → y ∈ P₀ ⊔ C := by
    intro y hyL hy3
    exact hK'G _ (mem_of_pow_three_eq_one_of_index_two (A' ⊔ C.subgroupOf L) hindex hyL hy3)
  have hCO : C ≤ CFSG.Open.GLBPrimeCore 3 M := le_glbPrimeCore_of hCM hCn hcop
  have hOM : CFSG.Open.GLBPrimeCore 3 M ≤ M := sSup_le fun _ hN => hN.1
  have hsub : P₀ ⊔ CFSG.Open.GLBPrimeCore 3 M ≤ M := sup_le hP₀M hOM
  have hPC : P₀ ⊔ C ≤ P₀ ⊔ CFSG.Open.GLBPrimeCore 3 M := sup_le_sup le_rfl hCO
  refine ⟨P₀, hP₀L, hP₀card, ?_⟩
  rw [Subgroup.normal_subgroupOf_iff hsub]
  intro h m hh hm
  have hmap : (P₀ ⊔ CFSG.Open.GLBPrimeCore 3 M).map (MulAut.conj m).toMonoidHom ≤
      P₀ ⊔ CFSG.Open.GLBPrimeCore 3 M := by
    rw [Subgroup.map_sup]
    apply sup_le
    · apply Subgroup.map_le_iff_le_comap.2
      intro p hp
      have hp' : p ∈ Subgroup.zpowers (x : G) := by rw [← hP₀def]; exact hp
      have hmxL : m * (x : G) * m⁻¹ ∈ L :=
        (Subgroup.normal_subgroupOf_iff hLM).1 hLn (x : G) m x.2 hm
      have hcube : (m * (x : G) * m⁻¹) ^ 3 = 1 := by
        rw [conj_pow, hx3]
        group
      have hxP : (x : G) ∈ (P₀ ⊔ CFSG.Open.GLBPrimeCore 3 M).comap
          (MulAut.conj m).toMonoidHom := by
        rw [Subgroup.mem_comap]
        exact hPC (key _ hmxL hcube)
      exact (Subgroup.zpowers_le.2 hxP) hp'
    · apply Subgroup.map_le_iff_le_comap.2
      intro o ho
      rw [Subgroup.mem_comap]
      exact Subgroup.mem_sup_right (glbPrimeCore_conj_mem hm ho)
  have hfin : (MulAut.conj m).toMonoidHom h ∈ P₀ ⊔ CFSG.Open.GLBPrimeCore 3 M :=
    hmap ⟨h, hh, rfl⟩
  exact hfin

end CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs

end
