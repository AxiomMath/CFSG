module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.LeafC1Swap
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.LeafC1

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.F1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
  CFSG.GH74.GLS.Stage1.Thm3.Sec7
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G}

@[expose] def OddCommS (z : G) (S K₁ K₂ : Subgroup G) : Prop :=
  ∀ x ∈ centralizer ({z} : Set G), Odd (orderOf x) → ∀ s ∈ S, x * s * x⁻¹ * s⁻¹ ∈ K₁ ⊔ K₂ ⊔ Oz z

theorem interchanges_of_not_mem (h : Std4 G z S K₁ K₂) {t : G} (htC : t ∈ centralizer ({z} : Set G))
    (htn : t ∉ normalizer (K₁ : Set G)) : Interchanges t K₁ K₂ := by
  rcases IVK.Lifted.std4_perm_cmap h htC with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact absurd ((IVK.Lifted.cmap_eq_iff_normalizer K₁ t).1 h1) htn
  · refine ⟨?_, ?_⟩
    · show cmap t⁻¹ K₁ = K₂
      rw [← h2]; exact cmap_inv_cancel t K₂
    · show cmap t⁻¹ K₂ = K₁
      rw [← h1]; exact cmap_inv_cancel t K₁

theorem oddCommS_of (hII : II4_4_4_center) (h44 : II4_44) (h2A7 : IVK.Lifted.II4_2A7) (hFS : FStar_C)
    (h : Std4 G z S K₁ K₂) (hQ : Qz S z = zpowers z)
    (hswap : ∀ t ∈ S, Interchanges t K₁ K₂ → ∀ x ∈ centralizer ({z} : Set G), Odd (orderOf x) →
      x * t * x⁻¹ * t⁻¹ ∈ K₁ ⊔ K₂ ⊔ Oz z) : OddCommS z S K₁ K₂ := by
  intro x hxC hxodd s hsS
  have hM := m4_of_std hII h
  have hsC : s ∈ centralizer ({z} : Set G) := hM.S_syl.1 hsS
  obtain ⟨hx₁, hx₂⟩ := Leaf.odd_normalizes_comps h hxC hxodd
  by_cases hs1 : s ∈ normalizer (K₁ : Set G)
  · have hs2 : s ∈ normalizer (K₂ : Set G) := (IVK.Lifted.std4_normalizer_swap h hsC).1 hs1
    exact Leaf.comm_mem_of_normalizes h44 h2A7 hII hFS h hQ hxC hsC hx₁ hx₂ hs1 hs2
  · exact hswap s hsS (interchanges_of_not_mem h hsC hs1) x hxC hxodd

theorem oddCommS_of_S1 (hII : II4_4_4_center) (h44 : II4_44) (h2A7 : IVK.Lifted.II4_2A7)
    (hFS : FStar_C) (h : Std4 G z S K₁ K₂) (hQ : Qz S z = zpowers z)
    (hS : S ≤ normalizer (K₁ : Set G)) : OddCommS z S K₁ K₂ :=
  oddCommS_of hII h44 h2A7 hFS h hQ (fun t ht hI _ _ _ => by
    exfalso
    apply h.ne
    have h1 : conjugate K₁ t = K₁ := by
      show cmap t⁻¹ K₁ = K₁
      exact (IVK.Lifted.cmap_eq_iff_normalizer K₁ t⁻¹).2 ((normalizer (K₁ : Set G)).inv_mem (hS ht))
    rw [← hI.1, h1])

theorem L_norm (hII : II4_4_4_center) (h : Std4 G z S K₁ K₂) :
    ∀ c ∈ centralizer ({z} : Set G), ∀ l ∈ K₁ ⊔ K₂ ⊔ Oz z, c * l * c⁻¹ ∈ K₁ ⊔ K₂ ⊔ Oz z := by
  intro c hc l hl
  have hM := m4_of_std hII h
  have hK12 : K₁ ⊔ K₂ ≤ Cz z := sup_le hM.K₁_le hM.K₂_le
  obtain ⟨n, hn, o, ho, rfl⟩ := A.mem_sup_of_le_normalizer (le_normalizer_Oz hK12) hl
  have e : c * (n * o) * c⁻¹ = (c * n * c⁻¹) * (c * o * c⁻¹) := by group
  rw [e]
  exact mul_mem (Subgroup.mem_sup_left (hM.C_norm_K hc hn)) (Subgroup.mem_sup_right (Oz_conj hc ho))

theorem odd_normalizes_N (h : Std4 G z S K₁ K₂) (hxs : OddCommS z S K₁ K₂) {x : G}
    (hxC : x ∈ centralizer ({z} : Set G)) (hxo : Odd (orderOf x)) :
    ∀ n ∈ K₁ ⊔ K₂ ⊔ S ⊔ Oz z, x * n * x⁻¹ ∈ K₁ ⊔ K₂ ⊔ S ⊔ Oz z := by
  obtain ⟨hx₁, hx₂⟩ := Leaf.odd_normalizes_comps h hxC hxo
  have hN₀ : K₁ ⊔ K₂ ⊔ Oz z ≤ K₁ ⊔ K₂ ⊔ S ⊔ Oz z :=
    sup_le ((le_sup_left : K₁ ⊔ K₂ ≤ K₁ ⊔ K₂ ⊔ S).trans le_sup_left) le_sup_right
  have hSN : S ≤ K₁ ⊔ K₂ ⊔ S ⊔ Oz z := (le_sup_right : S ≤ K₁ ⊔ K₂ ⊔ S).trans le_sup_left
  let D : Subgroup G := (K₁ ⊔ K₂ ⊔ S ⊔ Oz z).comap (MulAut.conj x).toMonoidHom
  have hmemD : ∀ g : G, g ∈ D ↔ x * g * x⁻¹ ∈ K₁ ⊔ K₂ ⊔ S ⊔ Oz z := fun g => by
    simp [D, Subgroup.mem_comap, MulAut.conj_apply]
  have hK₁D : K₁ ≤ D := fun k hk => by
    rw [hmemD]
    exact mem_sup_left (mem_sup_left (mem_sup_left ((mem_normalizer_iff.1 hx₁ k).1 hk)))
  have hK₂D : K₂ ≤ D := fun k hk => by
    rw [hmemD]
    exact mem_sup_left (mem_sup_left (mem_sup_right ((mem_normalizer_iff.1 hx₂ k).1 hk)))
  have hOD : Oz z ≤ D := fun o ho => by
    rw [hmemD]
    exact mem_sup_right (Oz_conj hxC ho)
  have hSD : S ≤ D := fun s hs => by
    rw [hmemD]
    have e : x * s * x⁻¹ = (x * s * x⁻¹ * s⁻¹) * s := by group
    rw [e]
    exact mul_mem (hN₀ (hxs x hxC hxo s hs)) (hSN hs)
  have hND : K₁ ⊔ K₂ ⊔ S ⊔ Oz z ≤ D := sup_le (sup_le (sup_le hK₁D hK₂D) hSD) hOD
  intro n hn
  exact (hmemD n).1 (hND hn)

theorem N_normal (hII : II4_4_4_center) (h : Std4 G z S K₁ K₂) (hxs : OddCommS z S K₁ K₂) :
    ∀ c ∈ centralizer ({z} : Set G), ∀ n ∈ K₁ ⊔ K₂ ⊔ S ⊔ Oz z, c * n * c⁻¹ ∈ K₁ ⊔ K₂ ⊔ S ⊔ Oz z := by
  intro c hc n hn
  have hM := m4_of_std hII h
  have hSN' : S ≤ K₁ ⊔ K₂ ⊔ S ⊔ Oz z := (le_sup_right : S ≤ K₁ ⊔ K₂ ⊔ S).trans le_sup_left
  have hSnorm : S ≤ normalizer ((K₁ ⊔ K₂ ⊔ S ⊔ Oz z : Subgroup G) : Set G) :=
    hSN'.trans Subgroup.le_normalizer
  have hoddN : ∀ x ∈ Cz z, Odd (orderOf x) →
      x ∈ normalizer ((K₁ ⊔ K₂ ⊔ S ⊔ Oz z : Subgroup G) : Set G) := by
    intro x hx hxo
    rw [Subgroup.mem_normalizer_iff]
    intro m
    refine ⟨fun hm => odd_normalizes_N h hxs hx hxo m hm, fun hm => ?_⟩
    have hxio : Odd (orderOf x⁻¹) := by rwa [orderOf_inv]
    have := odd_normalizes_N h hxs ((Cz z).inv_mem hx) hxio _ hm
    simpa [mul_assoc] using this
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL : IsPGroup 2 (↥(Cz z) ⧸ oResidual 2 ↥(Cz z)) :=
    CFSG.RankThree.Transfer.isPGroup_quotient_of_oResidual_le _ le_rfl
  have hmap := CFSG.RankThree.Transfer.map_mk_eq_top_of_isPGroup (M.toSylow hM.S_syl)
    (oResidual 2 ↥(Cz z)) hL
  have hcmem : QuotientGroup.mk' (oResidual 2 ↥(Cz z)) (⟨c, hc⟩ : ↥(Cz z)) ∈
      ((M.toSylow hM.S_syl : Subgroup ↥(Cz z))).map (QuotientGroup.mk' (oResidual 2 ↥(Cz z))) := by
    rw [hmap]; exact Subgroup.mem_top _
  obtain ⟨s, hs, hsc⟩ := Subgroup.mem_map.1 hcmem
  have hsS : (s : G) ∈ S := (M.mem_toSylow hM.S_syl s.2).2 hs
  have hlmem : s⁻¹ * ⟨c, hc⟩ ∈ oResidual 2 ↥(Cz z) := QuotientGroup.eq.1 hsc
  have hLle : oResidual 2 ↥(Cz z) ≤
      (normalizer ((K₁ ⊔ K₂ ⊔ S ⊔ Oz z : Subgroup G) : Set G)).comap (Cz z).subtype := by
    rw [oResidual, Subgroup.closure_le]
    intro x hx
    have hx2 : Odd (orderOf (x : G)) := by
      rw [Subgroup.orderOf_coe]
      exact Nat.coprime_two_right.1 hx
    exact hoddN x x.2 hx2
  have hl : ((s⁻¹ * ⟨c, hc⟩ : ↥(Cz z)) : G) ∈
      normalizer ((K₁ ⊔ K₂ ⊔ S ⊔ Oz z : Subgroup G) : Set G) := hLle hlmem
  have hcnorm : c ∈ normalizer ((K₁ ⊔ K₂ ⊔ S ⊔ Oz z : Subgroup G) : Set G) := by
    have e : c = (s : G) * ((s⁻¹ * ⟨c, hc⟩ : ↥(Cz z)) : G) := by simp
    rw [e]
    exact mul_mem (hSnorm hsS) hl
  exact (Subgroup.mem_normalizer_iff.1 hcnorm n).1 hn

theorem oPrimeResidual_eq (hII : II4_4_4_center) (h : Std4 G z S K₁ K₂)
    (hN : ∀ c ∈ centralizer ({z} : Set G), ∀ n ∈ K₁ ⊔ K₂ ⊔ S ⊔ Oz z, c * n * c⁻¹ ∈ K₁ ⊔ K₂ ⊔ S ⊔ Oz z) :
    oPrimeResidual 2 (CentralizerBar z) =
      ((K₁ ⊔ K₂ ⊔ S).subgroupOf (centralizer ({z} : Set G))).map
        (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({z} : Set G)))) := by
  have hM := m4_of_std hII h
  refine le_antisymm ?_ (Leaf.N_image_le hII h)
  have hK₁C : K₁ ≤ Cz z := (h.comp_isPCompIn (Or.inl rfl)).1
  have hK₂C : K₂ ≤ Cz z := (h.comp_isPCompIn (Or.inr rfl)).1
  have hSC : S ≤ Cz z := hM.S_syl.1
  have hNC : K₁ ⊔ K₂ ⊔ S ≤ Cz z := sup_le (sup_le hK₁C hK₂C) hSC
  rw [oPrimeResidual, Subgroup.closure_le]
  rintro a ⟨k, hk⟩
  obtain ⟨c, rfl, j, hcj⟩ := Leaf.exists_two_lift (QuotientGroup.mk' (pPrimeCore 2 ↥(Cz z)))
    (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']; exact TwoThin.odd_card_pPrimeCore ↥(Cz z)) hk
  have hcj' : (c : G) ^ (2 ^ j) = 1 := by simpa using congrArg Subtype.val hcj
  have hzp : IsPGroup 2 ↥(zpowers (c : G)) := by
    have hdvd : orderOf (c : G) ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hcj'
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])
  obtain ⟨P', hP', hcP'⟩ := M.exists_syl2In_ge hzp (zpowers_le.2 c.2)
  obtain ⟨g, hgC, hg⟩ := M.Syl2In.exists_conj hM.S_syl hP'
  have hgcS : g * (c : G) * g⁻¹ ∈ S := by
    have := hcP' (mem_zpowers _)
    rw [hg, M.mem_cj] at this
    exact this
  have hgN : g⁻¹ * (g * (c : G) * g⁻¹) * g⁻¹⁻¹ ∈ K₁ ⊔ K₂ ⊔ S ⊔ Oz z :=
    hN g⁻¹ (inv_mem hgC) _ (mem_sup_left (mem_sup_right hgcS))
  have hcN : (c : G) ∈ K₁ ⊔ K₂ ⊔ S ⊔ Oz z := by
    have e : g⁻¹ * (g * (c : G) * g⁻¹) * g⁻¹⁻¹ = c := by group
    rwa [e] at hgN
  obtain ⟨n, hn, o, ho, hno⟩ := A.mem_sup_of_le_normalizer (le_normalizer_Oz hNC) hcN
  have hoC : o ∈ Cz z := TwoThin.pPrimeCoreOf_le (Cz z) ho
  have hnC : n ∈ Cz z := hNC hn
  refine ⟨⟨n, hnC⟩, hn, ?_⟩
  have e1 : (c : ↥(Cz z)) = ⟨n, hnC⟩ * ⟨o, hoC⟩ := Subtype.ext hno
  rw [e1, map_mul]
  have : QuotientGroup.mk' (pPrimeCore 2 ↥(Cz z)) ⟨o, hoC⟩ = 1 :=
    (hatMk_eq_one_iff (Cz z) ⟨o, hoC⟩).2 ho
  rw [this, mul_one]

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.F1
