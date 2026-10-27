module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7B
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitConjOrbit

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer DihedralGroup
open scoped Pointwise

namespace A7Base

variable {X : Type} [Group X] [Finite X] (S : A7Base X)

theorem card_T_eq_two_pow :
    Nat.card S.data.T = 2 ^ (Nat.card (centralizer ({S.t} : Set X))).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [A7Data.T, Config.sylowIn, card_map_of_injective (subtype_injective _),
    Sylow.card_eq_multiplicity]

theorem card_T_eq_two_pow_of_conj {b g : X} (hgb : g * S.t * g⁻¹ = b) :
    Nat.card S.data.T = 2 ^ (Nat.card (centralizer ({b} : Set X))).factorization 2 := by
  have hC : centralizer ({b} : Set X) =
      (centralizer ({S.t} : Set X)).map (MulAut.conj g).toMonoidHom := by
    ext c
    rw [mem_centralizer_singleton_iff]
    constructor
    · intro hc
      refine ⟨g⁻¹ * c * g, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      rw [← hgb] at hc
      calc g⁻¹ * c * g * S.t = g⁻¹ * (c * (g * S.t * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * S.t * g⁻¹) * c) * g := by rw [hc]
        _ = S.t * (g⁻¹ * c * g) := by group
    · rintro ⟨d, hd, rfl⟩
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hd
      rw [← hgb]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc g * d * g⁻¹ * (g * S.t * g⁻¹) = g * (d * S.t) * g⁻¹ := by group
        _ = g * (S.t * d) * g⁻¹ := by rw [hd]
        _ = g * S.t * g⁻¹ * (g * d * g⁻¹) := by group
  rw [S.card_T_eq_two_pow, hC, card_map_of_injective (MulAut.conj g).injective]

theorem exists_normalizer_conj_eq {b : X} (hb : b ∈ S.B) (hconj : ConjTo S.t b) :
    ∃ n ∈ normalizer (S.data.T : Set X), n * S.t * n⁻¹ = b := by
  obtain ⟨g, hgb⟩ := hconj
  have hTb : S.data.T ≤ centralizer ({b} : Set X) := fun h hh =>
    mem_centralizer_singleton_iff.mpr (S.central_of_mem_B hb hh).symm
  have hgTb : S.data.T.map (MulAut.conj g).toMonoidHom ≤ centralizer ({b} : Set X) := by
    rintro _ ⟨h, hh, rfl⟩
    rw [mem_centralizer_singleton_iff, ← hgb]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have := S.data.commute_t hh
    calc g * h * g⁻¹ * (g * S.t * g⁻¹) = g * (h * S.t) * g⁻¹ := by group
      _ = g * (S.t * h) * g⁻¹ := by rw [this]
      _ = g * S.t * g⁻¹ * (g * h * g⁻¹) := by group
  have hcard := S.card_T_eq_two_pow_of_conj hgb
  obtain ⟨c, hc, hcT⟩ := exists_conj_eq_of_card_eq hgTb hTb
    (by rw [card_map_of_injective (MulAut.conj g).injective, hcard]) hcard
  refine ⟨c * g, ?_, ?_⟩
  · rw [mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have : c * (g * h * g⁻¹) * c⁻¹ ∈ S.data.T := by
        rw [← hcT]
        exact ⟨g * h * g⁻¹, ⟨h, hh, rfl⟩, rfl⟩
      simpa [mul_assoc] using this
    · intro hh
      have h1 : c * g * h * (c * g)⁻¹ ∈ (S.data.T.map (MulAut.conj g).toMonoidHom).map
          (MulAut.conj c).toMonoidHom := by rw [hcT]; exact hh
      obtain ⟨_, ⟨h', hh', rfl⟩, he⟩ := h1
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at he
      have : h' = h := by
        have := congrArg (fun y => (c * g)⁻¹ * y * (c * g)) he
        rw [show (c * g)⁻¹ * (c * (g * h' * g⁻¹) * c⁻¹) * (c * g) = h' by group,
          show (c * g)⁻¹ * (c * g * h * (c * g)⁻¹) * (c * g) = h by group] at this
        exact this
      rw [← this]
      exact hh'
  · have hcb : c * b * c⁻¹ = b := by
      have := mem_centralizer_singleton_iff.mp hc
      calc c * b * c⁻¹ = b * c * c⁻¹ := by rw [this]
        _ = b := by group
    calc c * g * S.t * (c * g)⁻¹ = c * (g * S.t * g⁻¹) * c⁻¹ := by group
      _ = b := by rw [hgb, hcb]

theorem not_conjTo_of_le_centralizer {b : X} {Q : Subgroup X} (hQ : IsPGroup 2 Q)
    (hTQ : S.data.T < Q) (hQb : Q ≤ centralizer ({b} : Set X)) : ¬ ConjTo S.t b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro ⟨g, hgb⟩
  have hcard := S.card_T_eq_two_pow_of_conj hgb
  have hQ' : IsPGroup 2 (Q.subgroupOf (centralizer ({b} : Set X))) :=
    hQ.comap_of_injective _ (subtype_injective _)
  obtain ⟨P, hP⟩ := hQ'.exists_le_sylow
  have h1 : Nat.card Q ≤ Nat.card S.data.T := by
    rw [hcard, ← Sylow.card_eq_multiplicity P, ← Nat.card_congr (subgroupOfEquivOfLe hQb).toEquiv]
    exact Subgroup.card_le_of_le hP
  exact absurd h1 (not_le.mpr (Subgroup.card_lt_of_lt hTQ))

theorem B_eq_sup : S.B = ⊥ ⊔ zpowers S.z ⊔ zpowers S.t ⊔ zpowers S.k := by
  apply le_antisymm
  · rw [B, closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact mem_sup_left (mem_sup_left (mem_sup_right (mem_zpowers _)))
    · exact mem_sup_left (mem_sup_right (mem_zpowers _))
    · exact mem_sup_right (mem_zpowers _)
  · refine sup_le (sup_le (sup_le bot_le ?_) ?_) ?_ <;> rw [zpowers_le, B] <;>
      exact subset_closure (by simp)

theorem card_B : Nat.card S.B = 8 := by
  have hz2 : S.z ^ 2 = 1 := S.sq_of_mem_B (subset_closure (by simp))
  obtain ⟨hV1, hV1m, hV1c⟩ := ElemAbelianTwo.bot.sup_zpowers hz2
    (fun h => S.z_ne_one (mem_bot.mp h)) (fun a ha => by rw [mem_bot.mp ha, one_mul, mul_one])
  have hV1R : (⊥ ⊔ zpowers S.z : Subgroup X) ≤ S.data.R :=
    sup_le bot_le (zpowers_le.mpr S.z_mem)
  obtain ⟨hV2, hV2m, hV2c⟩ := hV1.sup_zpowers S.t_sq (fun h => S.data.t_not_mem_L (hV1R h).2)
    (fun a ha => S.data.commute_t (hV1R ha).1 |>.symm)
  have hkV2 : S.k ∉ (⊥ ⊔ zpowers S.z ⊔ zpowers S.t : Subgroup X) := by
    intro h
    rcases hV2m _ h with h1 | h1
    · exact S.k_not_mem_R (hV1R h1)
    · have h2 : S.k * S.t ∈ S.data.R := hV1R h1
      have hm : S.k * S.t ∈ S.data.T := mul_mem S.k_mem S.data.t_mem_T
      have h3 : S.data.ψ ⟨S.k * S.t, hm⟩ = c0 := by
        have : (⟨S.k * S.t, hm⟩ : S.data.T) = ⟨S.k, S.k_mem⟩ * ⟨S.t, S.data.t_mem_T⟩ := rfl
        rw [this, map_mul, S.ψ_k, S.ψ_t, mul_one]
      exact c0_not_mem_R0 (h3 ▸ S.data.ψ_mem_R0 h2)
  have hV2T : (⊥ ⊔ zpowers S.z ⊔ zpowers S.t : Subgroup X) ≤ S.data.T :=
    sup_le (hV1R.trans inf_le_left) (zpowers_le.mpr S.data.t_mem_T)
  obtain ⟨-, -, hV3c⟩ := hV2.sup_zpowers S.k_sq hkV2 (fun a ha =>
    S.central_of_mem_B (show S.k ∈ S.B from subset_closure (by simp)) (hV2T ha))
  rw [S.B_eq_sup, hV3c, hV2c, hV1c, Subgroup.card_bot]

theorem ψ_tk : S.data.ψ ⟨S.t * S.k, mul_mem S.data.t_mem_T S.k_mem⟩ = c0 := by
  have : (⟨S.t * S.k, mul_mem S.data.t_mem_T S.k_mem⟩ : S.data.T) =
      ⟨S.t, S.data.t_mem_T⟩ * ⟨S.k, S.k_mem⟩ := rfl
  rw [this, map_mul, S.ψ_t, S.ψ_k, one_mul]

theorem tk_not_mem_R : S.t * S.k ∉ S.data.R := fun h =>
  c0_not_mem_R0 (S.ψ_tk ▸ S.data.ψ_mem_R0 h)

theorem eq_of_mem_tk {c : X} (hc : c ∈ (zpowers S.t ⊔ zpowers S.k : Subgroup X)) :
    c = 1 ∨ c = S.t ∨ c = S.k ∨ c = S.t * S.k := by
  have hN : zpowers S.k ≤ normalizer (zpowers S.t : Set X) := by
    rw [zpowers_le]
    refine centralizer_le_normalizer _ ?_
    rw [mem_centralizer_iff]
    intro a ha
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp ha
    exact ((Commute.zpow_left (S.data.commute_t S.k_mem).symm n)).eq
  have hc' : c ∈ (zpowers S.t : Set X) * (zpowers S.k : Set X) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ hN]
    exact hc
  obtain ⟨a, ha, b, hb, rfl⟩ := hc'
  rcases eq_one_or_eq_of_mem_zpowers S.t_sq ha with rfl | rfl <;>
    rcases eq_one_or_eq_of_mem_zpowers S.k_sq hb with rfl | rfl <;> simp

theorem exists_fix_B {w : X} (hw : w ∈ normalizer (S.data.T : Set X)) (hw2 : w ^ 2 ∈ S.data.T)
    (hwt : w * S.t * w⁻¹ ≠ S.t) :
    ∃ c : X, (c = S.k ∨ c = S.t * S.k) ∧
      ∀ b ∈ S.B, w * b * w⁻¹ = b ↔ (b = 1 ∨ b = S.z ∨ b = c ∨ b = S.z * c) := by
  classical
  set A : Subgroup X := S.B ⊓ centralizer ({w} : Set X) with hA
  have hAB : A ≤ S.B := inf_le_left
  have hmemA : ∀ b, b ∈ A ↔ b ∈ S.B ∧ w * b * w⁻¹ = b := by
    intro b
    rw [hA, mem_inf, mem_centralizer_singleton_iff]
    refine and_congr_right fun _ => ⟨fun h => ?_, fun h => ?_⟩
    · calc w * b * w⁻¹ = b * w * w⁻¹ := by rw [h]
        _ = b := by group
    · calc b * w = w * b * w⁻¹ * w := by rw [h]
        _ = w * b := by group
  have hff : ∀ b ∈ S.B, w * (w * b * w⁻¹) * w⁻¹ = b := by
    intro b hb
    have := S.central_of_mem_B hb hw2
    calc w * (w * b * w⁻¹) * w⁻¹ = w ^ 2 * b * (w ^ 2)⁻¹ := by rw [pow_two]; group
      _ = b := by rw [← this]; group
  have hBc : ∀ a ∈ S.B, ∀ b ∈ S.B, a * b = b * a := fun a ha b hb =>
    S.central_of_mem_B ha (S.B_le_T hb)
  set g : S.B →* S.B :=
    { toFun := fun b => ⟨b * (w * b * w⁻¹), mul_mem b.2 (S.conj_mem_B hw b.2)⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by
        ext
        simp only [Subgroup.coe_mul]
        have h1 := hBc _ (S.conj_mem_B hw a.2) _ b.2
        calc (a : X) * b * (w * (a * b) * w⁻¹) = a * (b * (w * a * w⁻¹)) * (w * b * w⁻¹) := by
              group
          _ = a * ((w * a * w⁻¹) * b) * (w * b * w⁻¹) := by rw [h1]
          _ = a * (w * a * w⁻¹) * (b * (w * b * w⁻¹)) := by group } with hg
  have hker : g.ker = A.subgroupOf S.B := by
    ext b
    rw [MonoidHom.mem_ker, mem_subgroupOf, hmemA]
    have hb2 : (b : X) ^ 2 = 1 := S.sq_of_mem_B b.2
    have hbinv : (b : X)⁻¹ = b := by rw [inv_eq_iff_mul_eq_one, ← pow_two, hb2]
    constructor
    · intro h
      refine ⟨b.2, ?_⟩
      have h1 : (b : X) * (w * b * w⁻¹) = 1 := congrArg Subtype.val h
      have h2 := eq_inv_of_mul_eq_one_right h1
      rwa [hbinv] at h2
    · intro h
      ext
      change (b : X) * (w * b * w⁻¹) = 1
      rw [h.2, ← pow_two, hb2]
  have hrange : g.range ≤ A.subgroupOf S.B := by
    rintro _ ⟨b, rfl⟩
    rw [mem_subgroupOf, hmemA]
    refine ⟨mul_mem b.2 (S.conj_mem_B hw b.2), ?_⟩
    change w * (b * (w * b * w⁻¹)) * w⁻¹ = b * (w * b * w⁻¹)
    have h1 := hff b b.2
    calc w * ((b : X) * (w * b * w⁻¹)) * w⁻¹ = (w * b * w⁻¹) * (w * (w * b * w⁻¹) * w⁻¹) := by
          group
      _ = (w * b * w⁻¹) * b := by rw [h1]
      _ = b * (w * b * w⁻¹) := hBc _ (S.conj_mem_B hw b.2) _ b.2
  have hcardA : Nat.card A = 4 := by
    have h1 : Nat.card g.ker * Nat.card g.range = Nat.card S.B := by
      rw [← Subgroup.index_ker, Subgroup.card_mul_index]
    rw [hker, Nat.card_congr (subgroupOfEquivOfLe hAB).toEquiv, card_B] at h1
    have h2 : Nat.card g.range ≤ Nat.card A := by
      rw [← Nat.card_congr (subgroupOfEquivOfLe hAB).toEquiv]
      exact Subgroup.card_le_of_le hrange
    have h3 : Nat.card A ∣ 8 := card_B S ▸ Subgroup.card_dvd_of_le hAB
    have h4 : Nat.card A ≠ 8 := by
      intro h8
      have : A = S.B := Subgroup.eq_of_le_of_card_ge hAB (by rw [h8, card_B])
      have htA : S.t ∈ A := this ▸ (subset_closure (by simp) : S.t ∈ S.B)
      exact hwt ((hmemA _).mp htA).2
    have hmem : Nat.card A ∈ Nat.divisors 8 := Nat.mem_divisors.mpr ⟨h3, by norm_num⟩
    rw [show Nat.divisors 8 = {1, 2, 4, 8} by decide] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h
    · rw [h] at h1 h2; nlinarith
    · rw [h] at h1 h2; nlinarith
    · exact h
    · exact absurd h h4
  set V : Subgroup X := zpowers S.t ⊔ zpowers S.k with hV
  have hVB : V ≤ S.B := sup_le (zpowers_le.mpr (subset_closure (by simp)))
    (zpowers_le.mpr (subset_closure (by simp)))
  have hcardV : Nat.card V = 4 := by
    obtain ⟨eK, -, -⟩ := S.exists_equiv_tk
    rw [Nat.card_congr eK.toEquiv, DihedralGroup.nat_card]
  have hidxB : V.relIndex S.B = 2 := by
    have := relIndex_mul_card (H := V) (K := S.B)
    rw [inf_of_le_left hVB, hcardV, card_B] at this
    omega
  have hidxA : V.relIndex A ≤ 2 :=
    hidxB ▸ relIndex_le_of_le_right hAB (by rw [hidxB]; norm_num)
  have hcardVA : 2 ≤ Nat.card (V ⊓ A : Subgroup X) := by
    have := relIndex_mul_card (H := V) (K := A)
    rw [hcardA] at this
    have hpos : 0 < V.relIndex A := Nat.pos_of_ne_zero (by
      intro h0; rw [h0, zero_mul] at this; norm_num at this)
    by_contra hlt
    push Not at hlt
    have : V.relIndex A * Nat.card (V ⊓ A : Subgroup X) ≤ 2 * 1 :=
      Nat.mul_le_mul hidxA (by omega)
    omega
  obtain ⟨c, hcVA, hc1⟩ : ∃ c ∈ (V ⊓ A : Subgroup X), c ≠ 1 := by
    by_contra hne
    push Not at hne
    have : (V ⊓ A : Subgroup X) = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hne
    rw [this, Subgroup.card_bot] at hcardVA
    norm_num at hcardVA
  obtain ⟨hcV, hcA⟩ := mem_inf.mp hcVA
  have hct : c ≠ S.t := fun h => hwt ((hmemA _).mp (h ▸ hcA)).2
  have hck : c = S.k ∨ c = S.t * S.k := by
    rcases S.eq_of_mem_tk hcV with h | h | h | h
    · exact absurd h hc1
    · exact absurd h hct
    · exact Or.inl h
    · exact Or.inr h
  refine ⟨c, hck, fun b hb => ?_⟩
  have hcR : c ∉ S.data.R := by
    rcases hck with rfl | rfl
    · exact S.k_not_mem_R
    · exact S.tk_not_mem_R
  have hzA : S.z ∈ A := (hmemA _).mpr ⟨subset_closure (by simp), S.conj_z_eq hw⟩
  set s : Finset X := {1, S.z, c, S.z * c} with hs
  have hsA : (s : Set X) ⊆ A := by
    intro b hb
    simp only [hs, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact hzA
    · exact hcA
    · exact mul_mem hzA hcA
  have hcard_s : s.card = 4 := by
    have h1 : S.z ≠ c := fun h => hcR (h ▸ S.z_mem)
    have h2 : (1 : X) ≠ c := fun h => hcR (h ▸ one_mem _)
    have h3 : (1 : X) ≠ S.z * c := fun h => hcR (by
      have : c = S.z⁻¹ := eq_inv_of_mul_eq_one_right h.symm
      rw [this]
      exact inv_mem S.z_mem)
    have h4 : S.z ≠ S.z * c := fun h => hc1 (by
      have := mul_left_cancel (h.symm.trans (mul_one S.z).symm)
      exact this)
    have h5 : c ≠ S.z * c := fun h => S.z_ne_one (by
      have := mul_right_cancel (h.symm.trans (one_mul c).symm)
      exact this)
    rw [hs, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_singleton]
    · simpa using h5
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨h1, h4⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => S.z_ne_one h.symm, h2, h3⟩
  have hAeq : (A : Set X) = s := by
    symm
    refine Set.eq_of_subset_of_ncard_le hsA ?_ (Set.toFinite _)
    rw [Set.ncard_coe_finset, hcard_s, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hcardA]
  constructor
  · intro hb'
    have : b ∈ (A : Set X) := (hmemA b).mpr ⟨hb, hb'⟩
    rw [hAeq] at this
    simpa [hs] using this
  · intro hb'
    have : b ∈ (s : Set X) := by simpa [hs] using hb'
    exact ((hmemA b).mp (hsA this)).2

end A7Base

end CFSG.ComponentClassification.HSFLit
