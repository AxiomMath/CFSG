module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevExcAut
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevExcU33Cent
public import CFSG.GroupTheory.OppositeRadicals
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.Quasithin.Recognition.G2AmalE8Model

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.ABGLocalTools CFSG.Quasithin CFSG.Sporadic.Bridge Subgroup

private theorem u33J_eq_range :
    u33J = u33PresHom.range := by
  rw [range_u33PresHom]
  rfl

private theorem u33J_le_g2CG :
    u33J ≤ g2CG := by
  intro x hx
  rw [u33J_eq_range] at hx
  obtain ⟨y, rfl⟩ := hx
  exact u33PresHom_mem_g2CG y

private theorem u33XE_mem_u33J_of_lt
    {i : ℕ} (hi : i < 32) : u33XE i ∈ u33J := by
  unfold u33XE
  rw [if_pos hi]
  unfold u33Tel
  exact wordProd_mem_pred (P := fun k => k < 3) (K := u33J)
    (fun k _ => u33GenP_mem k) (u33P_letters.1 i hi)

private theorem exists_u33XE_eq
    {σ : Equiv.Perm (Fin 28)} (hσ : σ ∈ Subgroup.closure u33KGens) :
    ∃ i < 64, RepL (u33XL i) σ := by
  refine closure_subset_of_right_closed (S := u33KGens)
      (P := {σ | ∃ i < 64, RepL (u33XL i) σ}) ?_ ?_ ?_ hσ
  · rintro s (rfl | rfl | rfl | rfl)
    · exact ⟨4, by norm_num, u33P_orders.1⟩
    · exact ⟨4, by norm_num, u33P_orders.2.1⟩
    · exact ⟨2, by norm_num, u33P_orders.2.2.1⟩
    · exact ⟨2, by norm_num, u33Pi_sq⟩
  · exact ⟨0, by norm_num, by rw [u33X_zero]; exact repL_one 28⟩
  · rintro p ⟨i, hi, hp⟩ s (rfl | rfl | rfl | rfl)
    · obtain ⟨⟨j, hj, hj'⟩, -⟩ := u33X_closed i hi
      exact ⟨j, hj, by rw [← hj']; exact repL_mul hp (u33_genTab_rep 0 (by norm_num))⟩
    · obtain ⟨-, ⟨j, hj, hj'⟩, -⟩ := u33X_closed i hi
      exact ⟨j, hj, by rw [← hj']; exact repL_mul hp (u33_genTab_rep 1 (by norm_num))⟩
    · obtain ⟨-, -, ⟨j, hj, hj'⟩, -⟩ := u33X_closed i hi
      exact ⟨j, hj, by rw [← hj']; exact repL_mul hp (u33_genTab_rep 2 (by norm_num))⟩
    · obtain ⟨-, -, -, ⟨j, hj, hj'⟩⟩ := u33X_closed i hi
      exact ⟨j, hj, by rw [← hj']; exact repL_mul hp u33_pi_rep⟩

private theorem isSylowOf_closure_u33KGens :
    IsSylowOf 2 (Subgroup.closure u33KGens) g2CG := by
  have hle : Subgroup.closure u33KGens ≤ g2CG := by
    refine (Subgroup.closure_le _).2 ?_
    rintro g (rfl | rfl | rfl | rfl)
    · exact u33PresHom_genPG 0 ▸ u33PresHom_mem_g2CG _
    · exact u33PresHom_genPG 1 ▸ u33PresHom_mem_g2CG _
    · exact u33PresHom_genPG 2 ▸ u33PresHom_mem_g2CG _
    · exact u33Pi_mem_g2CG
  have hcard : Nat.card (Subgroup.closure u33KGens) = 64 := u33_card_K
  have hindex : ((Subgroup.closure u33KGens).subgroupOf g2CG).index = 189 := by
    have h := Subgroup.card_mul_index ((Subgroup.closure u33KGens).subgroupOf g2CG)
    have hcard' : Nat.card ((Subgroup.closure u33KGens).subgroupOf g2CG) = 64 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
      exact hcard
    rw [hcard', card_g2P] at h
    omega
  rw [isSylowOf_iff]
  refine ⟨hle, IsPGroup.of_card (n := 6) (by rw [hcard]; norm_num), ?_⟩
  change ¬ 2 ∣ ((Subgroup.closure u33KGens).subgroupOf g2CG).index
  rw [hindex]
  norm_num

private theorem mem_u33J_iff_conj
    {m x : Equiv.Perm (Fin 28)} (hm : m ∈ g2CG) :
    x ∈ u33J ↔ m * x * m⁻¹ ∈ u33J := by
  have hmap : (g2F.range).map g2CG.subtype = u33J := by
    rw [MonoidHom.map_range]
    have hcomp : g2CG.subtype.comp g2F = u33PresHom := by
      apply MonoidHom.ext
      intro z
      exact g2F_coe z
    rw [hcomp]
    exact u33J_eq_range.symm
  have hf : ∀ {m x : Equiv.Perm (Fin 28)}, m ∈ g2CG → x ∈ u33J →
      m * x * m⁻¹ ∈ u33J := by
    intro m x hm hx
    rw [← hmap] at hx ⊢
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hx
    have hconj : (⟨m, hm⟩ : G2P) * n * (⟨m, hm⟩ : G2P)⁻¹ ∈ g2F.range :=
      g2_normal_range.conj_mem n hn ⟨m, hm⟩
    exact Subgroup.mem_map.mpr ⟨_, hconj, by simp⟩
  constructor
  · exact hf hm
  · intro hx
    have h := hf (m := m⁻¹) (x := m * x * m⁻¹) (g2CG.inv_mem hm) hx
    simpa [mul_assoc] using h

private theorem inf_centralizer_conj {m x : Equiv.Perm (Fin 28)}
    (hmJ : u33J.map (MulAut.conj m).toMonoidHom = u33J) :
    u33J ⊓ centralizer ({m * x * m⁻¹} : Set (Equiv.Perm (Fin 28))) =
      (u33J ⊓ centralizer ({x} : Set (Equiv.Perm (Fin 28)))).map
        (MulAut.conj m).toMonoidHom := by
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj m).injective, hmJ]
  have hcent : (centralizer ({x} : Set (Equiv.Perm (Fin 28)))).map
      (MulAut.conj m).toMonoidHom =
      centralizer ({m * x * m⁻¹} : Set (Equiv.Perm (Fin 28))) := by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨z, hz, rfl⟩
      calc (m * z * m⁻¹) * (m * x * m⁻¹)
          = m * (z * x) * m⁻¹ := by group
        _ = m * (x * z) * m⁻¹ := by rw [hz]
        _ = (m * x * m⁻¹) * (m * z * m⁻¹) := by group
    · intro hy
      refine ⟨m⁻¹ * y * m, ?_, ?_⟩
      · calc (m⁻¹ * y * m) * x
            = m⁻¹ * (y * (m * x * m⁻¹)) * m := by group
          _ = m⁻¹ * ((m * x * m⁻¹) * y) * m := by rw [hy]
          _ = x * (m⁻¹ * y * m) := by group
      · change m * (m⁻¹ * y * m) * m⁻¹ = y
        group
  rw [hcent]

private theorem exists_conj_sylow_u33
    {c : Equiv.Perm (Fin 28)} (hc : c ∈ g2CG) (hcJ : c ∉ u33J) (hc2 : c * c = 1) :
    ∃ (k c'' : Equiv.Perm (Fin 28)), k ∈ g2CG ∧
      c'' ∈ Subgroup.closure u33KGens ∧ c'' = k⁻¹ * c * k ∧
      c'' * c'' = 1 ∧ c'' ∉ u33J := by
  have hS0 : IsSylowOf 2 (Subgroup.closure u33KGens) g2CG :=
    isSylowOf_closure_u33KGens
  let c' : G2P := ⟨c, hc⟩
  have hc'2 : c' * c' = 1 := Subtype.ext (by simpa using hc2)
  have hP : IsPGroup 2 (Subgroup.zpowers c') := by
    rintro ⟨g, hg⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    refine ⟨1, Subtype.ext ?_⟩
    have h2 : c' ^ (2 : ℤ) = 1 := by rw [zpow_two, hc'2]
    have h3 : (c' ^ n) * (c' ^ n) = 1 := by
      rw [← zpow_add, ← two_mul, zpow_mul, h2, one_zpow]
    simpa [pow_one, sq] using h3
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  let T : Subgroup (Equiv.Perm (Fin 28)) := (Q : Subgroup G2P).map g2CG.subtype
  have hT : IsSylowOf 2 T g2CG := ⟨Q, rfl⟩
  have hcT : c ∈ T :=
    Subgroup.mem_map.mpr ⟨c', hQ (Subgroup.mem_zpowers c'), rfl⟩
  obtain ⟨k, hk, hkconj⟩ := IsSylowOf.exists_mem_conj hS0 hT
  let c'' : Equiv.Perm (Fin 28) := k⁻¹ * c * k
  have hc''S0 : c'' ∈ Subgroup.closure u33KGens := (hkconj c).mp hcT
  have hc''2 : c'' * c'' = 1 := by
    dsimp [c'']
    calc (k⁻¹ * c * k) * (k⁻¹ * c * k) = k⁻¹ * (c * c) * k := by group
      _ = 1 := by rw [hc2]; group
  have hc''J : c'' ∉ u33J := by
    intro h
    apply hcJ
    have hiff := mem_u33J_iff_conj (m := k⁻¹) (x := c) (g2CG.inv_mem hk)
    rw [inv_inv] at hiff
    exact hiff.mpr (by simpa [c''] using h)
  exact ⟨k, c'', hk, hc''S0, rfl, hc''2, hc''J⟩

private theorem exists_conj_pi_u33
    {c'' : Equiv.Perm (Fin 28)} (hc''S0 : c'' ∈ Subgroup.closure u33KGens)
    (hc''J : c'' ∉ u33J) (hc''2 : c'' * c'' = 1) :
    ∃ W : Equiv.Perm (Fin 28), W ∈ u33J ∧ c'' = W * u33Pi * W⁻¹ := by
  obtain ⟨i, hi, hrep''⟩ := exists_u33XE_eq hc''S0
  have hc''eq : c'' = u33XE i := eq_of_repL hrep'' (u33X_rep i hi)
  have hi32 : 32 ≤ i := by
    by_contra h
    have hi' : i < 32 := by omega
    exact hc''J (by rw [hc''eq]; exact u33XE_mem_u33J_of_lt hi')
  have hsq : compL (u33XL i) (u33XL i) = List.range 28 := by
    have hrep : RepL (compL (u33XL i) (u33XL i)) (c'' * c'') := by
      rw [hc''eq]
      exact repL_mul (u33X_rep i hi) (u33X_rep i hi)
    rw [hc''2] at hrep
    exact repL_unique hrep (repL_one 28)
  let w : String := GomiExcU33.u33OutWords.getD (i - 32) ""
  let W : Equiv.Perm (Fin 28) := wordProd u33GenP (u33W w)
  have hw : ∀ l ∈ u33W w, l.1 < 5 := by
    have hlen : GomiExcU33.u33OutWords.length = 32 :=
      GomiExcU33.u33Words_length.2.2
    have hidx : i - 32 < GomiExcU33.u33OutWords.length := by omega
    have hwmem : w ∈ GomiExcU33.u33OutWords := by
      dsimp [w]
      rw [List.getD_eq_getElem _ _ hidx]
      exact List.getElem_mem _
    exact GomiExcU33.u33Words_letters.2.2 w hwmem
  have hrepW : RepL (GomiExcU33.u33ConjL (u33W w) u33PiTab) (W * u33Pi * W⁻¹) :=
    GomiExcU33.repL_u33ConjL hw u33_pi_rep
  have hconj_eq : GomiExcU33.u33ConjL (u33W w) u33PiTab = u33XL i :=
    GomiExcU33.u33OutWords_conj i hi hi32 hsq
  have hc''W : c'' = W * u33Pi * W⁻¹ := by
    refine eq_of_repL hrep'' ?_
    rw [← hconj_eq]
    exact hrepW
  exact ⟨W, wordProd_mem (fun j => u33GenP_mem j) _, hc''W⟩

private theorem eqLocus_map_u33
    (c : G2P) :
    u33J ⊓ centralizer ({(c : Equiv.Perm (Fin 28))} : Set (Equiv.Perm (Fin 28))) =
      ((g2E8Action c).toMonoidHom.eqLocus (MonoidHom.id U33G)).map u33PresHom := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxJ, hxC⟩ := Subgroup.mem_inf.mp hx
    rw [u33J_eq_range] at hxJ
    obtain ⟨y, rfl⟩ := hxJ
    refine Subgroup.mem_map.mpr ⟨y, ?_, rfl⟩
    change g2E8Action c y = y
    apply g2_indexTwo.inj
    rw [g2F_action]
    have hcomm : u33PresHom y * c = c * u33PresHom y :=
      Subgroup.mem_centralizer_singleton_iff.mp hxC
    have hcomm' : g2F y * c = c * g2F y := by
      apply Subtype.ext
      simpa [g2F_coe] using hcomm
    have hcomm'' : c * g2F y = g2F y * c := hcomm'.symm
    rw [hcomm'']
    group
  · rintro ⟨y, hy, rfl⟩
    have hy' : g2E8Action c y = y := hy
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [u33J_eq_range]
      exact ⟨y, rfl⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have h := g2F_action c y
      rw [hy'] at h
      have h2 : g2F y * c = c * g2F y := by
        calc g2F y * c = (c * g2F y * c⁻¹) * c := congrArg (· * c) h
          _ = c * g2F y := by group
      have h2' := congrArg (fun z : G2P => (z : Equiv.Perm (Fin 28))) h2
      simpa [g2F_coe] using h2'

theorem GomiExcU33.pCoreOf_inf_centralizer_ne_bot_of_mem_g2CG
    {c : Equiv.Perm (Fin 28)}
    (hc : c ∈ g2CG) (hcJ : c ∉ u33J) (hc2 : c * c = 1) :
    pCoreOf 2 (u33J ⊓ centralizer ({c} : Set (Equiv.Perm (Fin 28)))) ≠ ⊥ := by
  obtain ⟨k, c'', hk, hc''S0, hc''eq, hc''2, hc''J⟩ :=
    exists_conj_sylow_u33 hc hcJ hc2
  obtain ⟨W, hWJ, hc''W⟩ := exists_conj_pi_u33 hc''S0 hc''J hc''2
  let m : Equiv.Perm (Fin 28) := k * W
  have hm : m ∈ g2CG := g2CG.mul_mem hk (u33J_le_g2CG hWJ)
  have hmJ : u33J.map (MulAut.conj m).toMonoidHom = u33J := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (mem_u33J_iff_conj hm).mp hy
    · intro hx
      refine ⟨m⁻¹ * x * m, ?_, ?_⟩
      · simpa using (mem_u33J_iff_conj (m := m⁻¹) (x := x) (g2CG.inv_mem hm)).mp hx
      · change m * (m⁻¹ * x * m) * m⁻¹ = x
        group
  have hc_eq : c = m * u33Pi * m⁻¹ := by
    calc c = k * c'' * k⁻¹ := by rw [hc''eq]; group
      _ = k * (W * u33Pi * W⁻¹) * k⁻¹ := by rw [hc''W]
      _ = m * u33Pi * m⁻¹ := by dsimp [m]; group
  rw [hc_eq, inf_centralizer_conj hmJ]
  rw [pCoreOf_map_of_injective 2 (MulAut.conj m).toMonoidHom (MulAut.conj m).injective]
  intro hbot
  exact GomiExcU33.pCoreOf_inf_centralizer_u33Pi_ne_bot
    ((Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj m).injective).mp hbot)

theorem gomiExcAutFixed_u33G :
    GomiExcAutFixed U33G := by
  intro β _ hβ2 hβout _ _ _
  obtain ⟨c, rfl⟩ := g2E8Action_bijective.2 β
  have hc2 : (c : Equiv.Perm (Fin 28)) * c = 1 := by
    have h : g2E8Action (c * c) = g2E8Action 1 := by
      rw [map_mul, hβ2, map_one]
    have h' : c * c = 1 := g2E8Action_bijective.1 h
    simpa using congrArg (fun x : G2P => (x : Equiv.Perm (Fin 28))) h'
  have hcJ : (c : Equiv.Perm (Fin 28)) ∉ u33J := by
    intro hcJ
    rw [u33J_eq_range] at hcJ
    obtain ⟨k, hk⟩ := hcJ
    have hck : g2F k = c := Subtype.ext (by rw [g2F_coe, hk])
    have hconj : g2E8Action c = MulAut.conj k := by
      ext x
      apply g2_indexTwo.inj
      rw [g2F_action, ← hck]
      simp [MulAut.conj_apply]
    exact hβout k hconj
  have hmap := eqLocus_map_u33 c
  have hne : pCoreOf 2
      (u33J ⊓ centralizer ({(c : Equiv.Perm (Fin 28))} : Set (Equiv.Perm (Fin 28)))) ≠
      ⊥ :=
    GomiExcU33.pCoreOf_inf_centralizer_ne_bot_of_mem_g2CG c.2 hcJ hc2
  intro hbot
  apply hne
  rw [hmap, pCoreOf_map_of_injective 2 u33PresHom u33PresHom_injective, hbot]
  simp

end CFSG.GroupTheory
