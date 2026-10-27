module

public import CFSG.LocalAnalysis.EvenBN.Tits.Model.Centralizers
public import CFSG.Quasithin.Background.SmithB42Tits

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.Model

open Subgroup CFSG.Sporadic.Schreier.Tits
open CFSG.Quasithin (tπ twoF4S twoF4H twoF4N twoF4P)

theorem card_le_of_elemAbelian_titsA
    {X : Subgroup (Equiv.Perm (Fin 1755))} (hX : X ≤ titsA)
    (hc : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a) (h2 : ∀ a ∈ X, a * a = 1) :
    X ≤ titsD ∧ Nat.card X ≤ 2 ^ 5 := by
  have hXD : X ≤ titsD := by
    intro a ha
    by_cases ha1 : a = 1
    · rw [ha1]
      exact one_mem _
    · exact titsA_involution_mem_D (hX ha) (orderOf_eq_prime (by rw [sq]; exact h2 a ha) ha1)
  refine ⟨hXD, ?_⟩
  have hE : CFSG.Quasithin.B42Disp.IsElem2 (X.subgroupOf titsD) := by
    refine ⟨fun a ha b hb => Subtype.ext (hc _ ha _ hb), fun a ha => Subtype.ext ?_⟩
    simpa [sq] using h2 _ ha
  have h := CFSG.Quasithin.B42Tits.card_le_of_isElem2 _ hE
  rwa [show Nat.card (X.subgroupOf titsD) = Nat.card X from
    Nat.card_congr (subgroupOfEquivOfLe hXD).toEquiv] at h

theorem conj_comm_mem_centralizer {G : Type*} [Group G] {P E : Subgroup G} {z c x : G}
    (hzP : ∀ y ∈ P, y * z = z * y)
    (hEP : ∀ e ∈ E, ∀ y ∈ P, e * y * e⁻¹ * y⁻¹ ∈ zpowers z)
    (hcE : ∀ e ∈ E, c * e = e * c) (hcz : c * z = z * c) (hxP : x ∈ P)
    (hcxP : c * x * c⁻¹ ∈ P) :
    c * x * c⁻¹ * x⁻¹ ∈ centralizer (E : Set G) := by
  rw [mem_centralizer_iff]
  intro e he
  have hζP : ∀ ζ ∈ zpowers z, ∀ y ∈ P, y * ζ = ζ * y := by
    intro ζ hζ y hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hζ
    exact (Commute.zpow_right (hzP y hy) k).eq
  have hζc : ∀ ζ ∈ zpowers z, c * ζ = ζ * c := by
    intro ζ hζ
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hζ
    exact (Commute.zpow_right hcz k).eq
  set a := c * x * c⁻¹ with ha
  set ζ := e * x * e⁻¹ * x⁻¹ with hζdef
  have hζ : ζ ∈ zpowers z := hEP e he x hxP
  have hea : e * a * e⁻¹ * a⁻¹ = ζ := by
    have hce : c * e * c⁻¹ = e := by rw [hcE e he, mul_inv_cancel_right]
    have hcei : c * e⁻¹ * c⁻¹ = e⁻¹ := by
      rw [← inv_inj, mul_inv_rev, mul_inv_rev, inv_inv, inv_inv, ← mul_assoc, hce]
    calc e * a * e⁻¹ * a⁻¹ = (c * e * c⁻¹) * a * (c * e⁻¹ * c⁻¹) * a⁻¹ := by rw [hce, hcei]
      _ = c * ζ * c⁻¹ := by rw [ha, hζdef]; group
      _ = ζ := by rw [hζc ζ hζ, mul_inv_cancel_right]
  have h1 : e * a = ζ * a * e := by
    calc e * a = (e * a * e⁻¹ * a⁻¹) * a * e := by group
      _ = ζ * a * e := by rw [hea]
  have h2 : e * x⁻¹ = x⁻¹ * ζ⁻¹ * e := by
    rw [hζdef]
    group
  have hy : a * x⁻¹ ∈ P := mul_mem hcxP (inv_mem hxP)
  calc e * (a * x⁻¹) = e * a * x⁻¹ := (mul_assoc _ _ _).symm
    _ = ζ * a * (e * x⁻¹) := by rw [h1]; group
    _ = ζ * a * (x⁻¹ * ζ⁻¹ * e) := by rw [h2]
    _ = ζ * (a * x⁻¹) * ζ⁻¹ * e := by group
    _ = a * x⁻¹ * e := by rw [← hζP ζ hζ _ hy]; group

@[expose] noncomputable def hatE :
    Subgroup (Equiv.Perm (Fin 1755)) :=
  closure {x | x ∈ twoF4P ∧ ∀ y ∈ twoF4P, x * y * x⁻¹ * y⁻¹ ∈ zpowers titsZ}

@[expose] noncomputable def hatF :
    Subgroup (Equiv.Perm (Fin 1755)) :=
  twoF4P ⊓ centralizer (hatE : Set (Equiv.Perm (Fin 1755)))

theorem twoF4_vertex
    :
    (∀ x, x ∈ hatE ↔ x ∈ twoF4P ∧ ∀ y ∈ twoF4P, x * y * x⁻¹ * y⁻¹ ∈ zpowers titsZ) ∧
      (∀ e ∈ hatE, e * e = 1) ∧ (∀ e ∈ hatE, ∀ e' ∈ hatE, e * e' = e' * e) ∧
      Nat.card twoF4P = 16 * Nat.card hatF ∧ Nat.card hatF ≤ 2 * Nat.card hatE ∧
      (∀ x ∈ hatE, (∀ y ∈ twoF4P, x * y = y * x) → x ∈ zpowers titsZ) ∧
      (∀ x ∈ twoF4P, ∀ y ∈ twoF4P, x * y * x⁻¹ * y⁻¹ ∈ hatF) ∧
      ∃ c ∈ twoF4H, c ^ 5 = 1 ∧ ∀ x ∈ twoF4P, x ∉ hatF → c * x * c⁻¹ * x⁻¹ ∉ hatF := by
  have hV := CFSG.Quasithin.twoF4VertexFacts
  unfold CFSG.Quasithin.TitsLikeVertexFacts at hV
  obtain ⟨E, F, hE, hF, hE2, hEc, hPF, hFE, hEZ, hPP, -, -, -, c, hcH, hc5, hcfix⟩ := hV
  rw [CFSG.Quasithin.pCoreOf_twoF4H] at hE hF hPF hPP hEZ hcfix
  have hZ : ∀ w, w ∈ CFSG.Open.quasithinOmegaOneCenter (twoF4H ⊓ twoF4N) ↔
      w ∈ zpowers titsZ := fun w => by
    rw [CFSG.Quasithin.mem_omegaOneCenter_twoF4HN_iff, mem_zpowers_of_orderOf_two orderOf_titsZ]
  have hEmem : ∀ x, x ∈ E ↔ x ∈ twoF4P ∧ ∀ y ∈ twoF4P, x * y * x⁻¹ * y⁻¹ ∈ zpowers titsZ :=
    fun x => by simp only [hE, hZ]
  have hEeq : hatE = E := by
    have hset : {x | x ∈ twoF4P ∧ ∀ y ∈ twoF4P, x * y * x⁻¹ * y⁻¹ ∈ zpowers titsZ} =
        (E : Set (Equiv.Perm (Fin 1755))) := by
      ext x
      simp only [Set.mem_ofPred_eq, SetLike.mem_coe, hEmem]
    rw [hatE, hset, closure_eq]
  have hFeq : hatF = F := by
    ext x
    rw [hF, hatF, mem_inf, mem_centralizer_iff, hEeq]
    exact and_congr_right fun _ => forall₂_congr fun e _ => eq_comm
  rw [hEeq, hFeq]
  exact ⟨hEmem, hE2, hEc, hPF, hFE, fun x hx hc => (hZ x).1 (hEZ x hx hc), hPP, c, hcH, hc5,
    hcfix⟩

theorem hatE_le_twoF4P
    : hatE ≤ twoF4P := fun x hx => ((twoF4_vertex.1 x).1 hx).1

theorem hatE_le_titsJ
    : hatE ≤ titsJ := by
  intro e he
  have heP := hatE_le_twoF4P he
  have heD : e ∈ titsD := by
    by_cases he1 : e = 1
    · rw [he1]
      exact one_mem _
    · exact titsA_involution_mem_D
        (twoF4H_le_titsA (CFSG.Quasithin.twoF4P_le_twoF4H heP))
        (orderOf_eq_prime (by rw [sq]; exact twoF4_vertex.2.1 e he) he1)
  rw [← (pCore_twoF4H).2.2.1]
  exact ⟨heP, heD⟩

theorem tits_vertex_hatE
    :
    (∀ x, x ∈ hatE ↔ x ∈ titsJ ∧ ∀ y ∈ titsJ, x * y * x⁻¹ * y⁻¹ ∈ zpowers titsZ) ∧
      Nat.card hatE = 32 ∧ titsJ ⊓ centralizer (hatE : Set (Equiv.Perm (Fin 1755))) = hatE ∧
      (∀ x ∈ hatE, (∀ y ∈ titsJ, x * y = y * x) → x ∈ zpowers titsZ) ∧
      (∀ x ∈ titsJ, ∀ y ∈ titsJ, x * y * x⁻¹ * y⁻¹ ∈ hatE) ∧
      (∃ j ∈ titsJ, j ∉ hatE ∧ j * j = 1) ∧
      (∀ j ∈ titsJ, j ∉ hatE → j * j = 1 → ∀ j' ∈ titsJ, j' ∉ hatE → j' * j' = 1 →
        ∃ h ∈ titsH, h * j * h⁻¹ = j') ∧
      ∃ c ∈ titsH, c ^ 5 = 1 ∧ ∀ x ∈ titsJ, x ∉ hatE → c * x * c⁻¹ * x⁻¹ ∉ hatE := by
  obtain ⟨hEmem, -, -, hPF, hFE, -, -, -⟩ := twoF4_vertex
  have hV := CFSG.Quasithin.titsVertexFacts
  unfold CFSG.Quasithin.TitsLikeVertexFacts at hV
  obtain ⟨E, F, hE, hF, hE2, hEc, hPF', -, hEZ, hPP, -, hj, htr, c, hcH, hc5, hcfix⟩ := hV
  rw [CFSG.Quasithin.pCoreOf_titsH] at hE hF hPF' hPP hEZ hj htr hcfix
  have hZ : ∀ w, w ∈ CFSG.Open.quasithinOmegaOneCenter (titsH ⊓ titsN) ↔
      w ∈ zpowers titsZ := fun w => by
    rw [CFSG.Quasithin.mem_omegaOneCenter_titsHN_iff, mem_zpowers_of_orderOf_two orderOf_titsZ]
  have hP : Nat.card twoF4P = 1024 := (pCore_twoF4H).2.1
  have hE32 : 32 ≤ Nat.card hatE := by omega
  have hle : hatE ≤ E := fun x hx => by
    rw [hE]
    exact ⟨hatE_le_titsJ hx, fun y hy => (hZ _).2
      (((hEmem x).1 hx).2 y (CFSG.Quasithin.le_extSub hy))⟩
  have hEJ : E ≤ titsJ := fun x hx => ((hE x).1 hx).1
  have hEle : Nat.card E ≤ 2 ^ 5 :=
    (card_le_of_elemAbelian_titsA (hEJ.trans (titsJ_le_titsD.trans titsD_le_titsA)) hEc hE2).2
  have hEle' : Nat.card E ≤ 32 := by simpa using hEle
  have hEeq : hatE = E := eq_of_le_of_card_ge hle (by omega)
  have hE32' : 32 ≤ Nat.card E := hEeq ▸ hE32
  have hJ : Nat.card titsJ = 512 := titsQJ_facts.2.2.2
  have hEF : E ≤ F := fun x hx => (hF x).2 ⟨hEJ hx, fun e he => hEc x hx e he⟩
  have hFeq : F = E := (eq_of_le_of_card_ge hEF (by rw [hJ] at hPF'; omega)).symm
  rw [hFeq] at hF hPP hj htr hcfix
  rw [hEeq]
  refine ⟨fun x => by rw [hE]; simp only [hZ], by omega, ?_,
    fun x hx hc => (hZ x).1 (hEZ x hx hc), hPP, hj, htr, c, hcH, hc5, hcfix⟩
  ext x
  rw [mem_inf, mem_centralizer_iff, hF]
  exact and_congr_right fun _ => forall₂_congr fun e _ => eq_comm

theorem card_hatE
    :
    hatE ≤ titsJ ∧ (∀ e ∈ hatE, e * e = 1) ∧ (∀ e ∈ hatE, ∀ e' ∈ hatE, e * e' = e' * e) ∧
      Nat.card hatE = 32 :=
  ⟨hatE_le_titsJ, twoF4_vertex.2.1, twoF4_vertex.2.2.1, tits_vertex_hatE.2.1⟩

theorem comm_mem_titsD {x y : Equiv.Perm (Fin 1755)}
    (hx : x ∈ titsA) (hy : y ∈ titsA) : x * y * x⁻¹ * y⁻¹ ∈ titsD := by
  have e : x * y * x⁻¹ * y⁻¹ = (x * y) * (x⁻¹ * y⁻¹) := by group
  rw [e, mul_mem_titsD_iff (mul_mem hx hy) (mul_mem (inv_mem hx) (inv_mem hy)),
    mul_mem_titsD_iff hx hy, mul_mem_titsD_iff (inv_mem hx) (inv_mem hy), inv_mem_iff,
    inv_mem_iff]

theorem twoF4P_le_titsA :
    twoF4P ≤ titsA :=
  CFSG.Quasithin.twoF4P_le_twoF4H.trans twoF4H_le_titsA

theorem comm_hatE
    :
    (∀ x ∈ twoF4P, ∀ y ∈ twoF4P, x * y * x⁻¹ * y⁻¹ ∈ hatE) ∧
      (∀ x ∈ hatE, ∀ y ∈ twoF4P, x * y * x⁻¹ * y⁻¹ ∈ zpowers titsZ) ∧
      ∃ x ∈ hatE, ∃ y ∈ titsJ, x * y * x⁻¹ * y⁻¹ = titsZ := by
  obtain ⟨hEmem, -, -, -, -, -, hPP, -⟩ := twoF4_vertex
  obtain ⟨-, h32, hCJ, hEZ, -⟩ := tits_vertex_hatE
  refine ⟨fun x hx y hy => ?_, fun x hx y hy => ((hEmem x).1 hx).2 y hy, ?_⟩
  · have hF := hPP x hx y hy
    have hD := comm_mem_titsD (twoF4P_le_titsA hx) (twoF4P_le_titsA hy)
    rw [← hCJ]
    refine ⟨?_, hF.2⟩
    rw [← (pCore_twoF4H).2.2.1]
    exact ⟨hF.1, hD⟩
  · by_contra hne
    have hne' : ∀ x ∈ hatE, ∀ y ∈ titsJ, x * y * x⁻¹ * y⁻¹ ≠ titsZ :=
      fun x hx y hy h => hne ⟨x, hx, y, hy, h⟩
    have hle : hatE ≤ zpowers titsZ := fun x hx => hEZ x hx fun y hy => by
      have hc := ((hEmem x).1 hx).2 y (CFSG.Quasithin.le_extSub hy)
      rcases (mem_zpowers_of_orderOf_two orderOf_titsZ).1 hc with h1 | h1
      · calc x * y = x * y * x⁻¹ * y⁻¹ * y * x := by group
          _ = y * x := by rw [h1]; group
      · exact absurd h1 (hne' x hx y hy)
    have hc := card_le_of_le hle
    rw [Nat.card_zpowers, orderOf_titsZ, h32] at hc
    omega

theorem titsZ_mem_hatE
    : titsZ ∈ hatE := by
  rw [twoF4_vertex.1]
  have hzH : titsZ ∈ titsH := titsS_le_titsH titsZ_mem_titsS
  have hzJ : titsZ ∈ titsJ := CHJ_le_J ⟨hzH, mem_centralizer_iff.2 fun j hj =>
    mem_centralizer_singleton_iff.1 (titsH_le_centralizer_z (titsJ_le_titsH hj))⟩
  refine ⟨CFSG.Quasithin.le_extSub hzJ, fun y hy => ?_⟩
  have hyz : y * titsZ = titsZ * y := mem_centralizer_singleton_iff.1
    (twoF4H_le_centralizer_titsZ (CFSG.Quasithin.twoF4P_le_twoF4H hy))
  have : titsZ * y * titsZ⁻¹ * y⁻¹ = 1 := by rw [← hyz]; group
  rw [this]
  exact one_mem _

theorem twoF4H_le_normalizer_hatE
    : twoF4H ≤ normalizer (hatE : Set (Equiv.Perm (Fin 1755))) := by
  intro h hh
  apply CFSG.Quasithin.mem_normalizer_of_forall_conj_mem_f4
  intro e he
  obtain ⟨heP, hc⟩ := (twoF4_vertex.1 e).1 he
  rw [twoF4_vertex.1]
  have hPn := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 twoF4H hh
  rw [CFSG.Quasithin.pCoreOf_twoF4H] at hPn
  refine ⟨(mem_normalizer_iff.1 hPn e).1 heP, fun y hy => ?_⟩
  have hy' : h⁻¹ * y * h ∈ twoF4P := by
    have := (mem_normalizer_iff.1 (inv_mem hPn) y).1 hy
    simpa using this
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (hc _ hy')
  have heq : h * e * h⁻¹ * y * (h * e * h⁻¹)⁻¹ * y⁻¹ =
      h * (e * (h⁻¹ * y * h) * e⁻¹ * (h⁻¹ * y * h)⁻¹) * h⁻¹ := by group
  have hhz : h * titsZ = titsZ * h :=
    mem_centralizer_singleton_iff.1 (twoF4H_le_centralizer_titsZ hh)
  rw [heq, ← hk, (Commute.zpow_right hhz k).eq, mul_inv_cancel_right]
  exact zpow_mem (mem_zpowers _) k

theorem twoF4H_centralizer_hatE_le
    : twoF4H ⊓ centralizer (hatE : Set (Equiv.Perm (Fin 1755))) ≤ twoF4P := by
  obtain ⟨hEmem, -, -, hPF, -, -, -, c, hcH, hc5, hcfix⟩ := twoF4_vertex
  have hP : Nat.card twoF4P = 1024 := (pCore_twoF4H).2.1
  have hH : Nat.card twoF4H = 20480 := card_twoF4H
  set Y := twoF4H ⊓ centralizer (hatE : Set (Equiv.Perm (Fin 1755))) with hYdef
  have hYn : twoF4H ≤ normalizer (Y : Set (Equiv.Perm (Fin 1755))) := by
    intro h hh
    apply CFSG.Quasithin.mem_normalizer_of_forall_conj_mem_f4
    intro y hy
    obtain ⟨hyH, hyC⟩ := mem_inf.1 hy
    refine mem_inf.2 ⟨mul_mem (mul_mem hh hyH) (inv_mem hh), mem_centralizer_iff.2 fun e he => ?_⟩
    have he' : h⁻¹ * e * h ∈ hatE := by
      have := (mem_normalizer_iff.1 (inv_mem (twoF4H_le_normalizer_hatE hh)) e).1 he
      simpa using this
    have h1 := mem_centralizer_iff.1 hyC _ he'
    calc e * (h * y * h⁻¹) = h * ((h⁻¹ * e * h) * y) * h⁻¹ := by group
      _ = h * (y * (h⁻¹ * e * h)) * h⁻¹ := by rw [h1]
      _ = h * y * h⁻¹ * e := by group
  have hnle : ¬ twoF4P ≤ hatF := fun h => by
    have := card_le_of_le h
    omega
  obtain ⟨x₀, hx₀P, hx₀F⟩ := Set.not_subset.1 hnle
  have hc1 : c ≠ 1 := by
    rintro rfl
    exact hcfix x₀ hx₀P hx₀F (by rw [one_mul, inv_one, mul_one, mul_inv_cancel]; exact one_mem _)
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hco : orderOf c = 5 := orderOf_eq_prime hc5 hc1
  have h5 : ∀ g ∈ Y, orderOf g ≠ 5 := by
    intro g hgY hg5
    set c' : twoF4H := ⟨c, hcH⟩ with hc'
    have hc'o : orderOf c' = 5 := by rw [← Subgroup.orderOf_coe]; exact hco
    have hPc : IsPGroup 5 (zpowers c') :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc'o, pow_one])
    have hidx : ¬ 5 ∣ (zpowers c').index := by
      have h := card_mul_index (zpowers c')
      rw [Nat.card_zpowers, hc'o, hH] at h
      have h' : (zpowers c').index = 4096 := by omega
      rw [h']
      norm_num
    set g' : twoF4H := ⟨g, hgY.1⟩ with hg'
    have hg'o : orderOf g' = 5 := by rw [← Subgroup.orderOf_coe]; exact hg5
    obtain ⟨h, hh⟩ := exists_conj_mem_sylow (hPc.toSylow hidx) (x := g')
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg'o, pow_one]))
    rw [IsPGroup.toSylow_coe] at hh
    have hyo : orderOf (h * g' * h⁻¹) = 5 := by
      have := orderOf_injective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective g'
      simpa [MulAut.conj_apply, hg'o] using this
    have hzy : zpowers (h * g' * h⁻¹) = zpowers c' := by
      apply eq_of_le_of_card_ge (zpowers_le.2 hh)
      rw [Nat.card_zpowers, Nat.card_zpowers, hyo, hc'o]
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (hzy ▸ mem_zpowers c' : c' ∈ zpowers (h * g' * h⁻¹))
    have hcY : c ∈ Y := by
      have h1 : (h : Equiv.Perm (Fin 1755)) * g * (h : Equiv.Perm (Fin 1755))⁻¹ ∈ Y :=
        (mem_normalizer_iff.1 (hYn h.2) g).1 hgY
      have h2 := zpow_mem h1 k
      have h3 : ((h * g' * h⁻¹ : twoF4H) : Equiv.Perm (Fin 1755)) ^ k = c :=
        by rw [← Subgroup.coe_zpow, hk]
      rw [← h3]
      exact h2
    have hcx : c * x₀ * c⁻¹ * x₀⁻¹ ∈ hatF := by
      have hPn := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 twoF4H hcH
      rw [CFSG.Quasithin.pCoreOf_twoF4H] at hPn
      have hcxP : c * x₀ * c⁻¹ ∈ twoF4P := (mem_normalizer_iff.1 hPn x₀).1 hx₀P
      refine mem_inf.2 ⟨mul_mem hcxP (inv_mem hx₀P), ?_⟩
      exact conj_comm_mem_centralizer (P := twoF4P) (E := hatE) (z := titsZ)
        (fun y hy => mem_centralizer_singleton_iff.1
          (twoF4H_le_centralizer_titsZ (CFSG.Quasithin.twoF4P_le_twoF4H hy)))
        (fun e he y hy => ((hEmem e).1 he).2 y hy)
        (fun e he => (mem_centralizer_iff.1 hcY.2 e he).symm)
        (mem_centralizer_singleton_iff.1 (twoF4H_le_centralizer_titsZ hcH)) hx₀P hcxP
    exact hcfix x₀ hx₀P hx₀F hcx
  have hp : IsPGroup 2 Y := by
    intro g
    have hdvd : orderOf (g : Equiv.Perm (Fin 1755)) ∣ 2 ^ 12 * 5 := by
      have := Subgroup.orderOf_dvd_natCard twoF4H g.2.1
      rwa [hH] at this
    have hn5 : ¬ 5 ∣ orderOf (g : Equiv.Perm (Fin 1755)) := by
      intro h5d
      have hfin : IsOfFinOrder (g : Equiv.Perm (Fin 1755)) := isOfFinOrder_of_finite _
      have := orderOf_pow_orderOf_div hfin.orderOf_pos.ne' h5d
      exact h5 _ (pow_mem g.2 _) this
    have hd2 : orderOf (g : Equiv.Perm (Fin 1755)) ∣ 2 ^ 12 :=
      (Nat.Coprime.dvd_of_dvd_mul_right
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 hn5).symm hdvd)
    refine ⟨12, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact orderOf_dvd_iff_pow_eq_one.1 hd2
  rw [← CFSG.Quasithin.pCoreOf_twoF4H]
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hYn hp

theorem titsA_centralizer_hatE
    :
    titsA ⊓ centralizer (hatE : Set (Equiv.Perm (Fin 1755))) = hatF ∧
      titsD ⊓ centralizer (hatE : Set (Equiv.Perm (Fin 1755))) = hatE ∧
      Nat.card hatF = 64 ∧ hatF ⊓ titsD = hatE ∧ (∀ a ∈ hatF, ∀ b ∈ hatF, a * b = b * a) ∧
      ∀ a ∈ hatF, a * a ∈ hatE := by
  obtain ⟨-, -, hEc, hPF, -, -, -, -⟩ := twoF4_vertex
  obtain ⟨-, -, hCJ, -⟩ := tits_vertex_hatE
  have hP : Nat.card twoF4P = 1024 := (pCore_twoF4H).2.1
  have hED : hatE ≤ titsD := hatE_le_titsJ.trans titsJ_le_titsD
  have hFD : hatF ⊓ titsD = hatE := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxF, hxD⟩ := mem_inf.1 hx
      obtain ⟨hxP, hxC⟩ := mem_inf.1 hxF
      rw [← hCJ]
      refine mem_inf.2 ⟨?_, hxC⟩
      rw [← (pCore_twoF4H).2.2.1]
      exact mem_inf.2 ⟨hxP, hxD⟩
    · intro x hx
      exact mem_inf.2 ⟨mem_inf.2 ⟨hatE_le_twoF4P hx, mem_centralizer_iff.2 fun e he =>
        hEc e he x hx⟩, hED hx⟩
  have hAF : titsA ⊓ centralizer (hatE : Set (Equiv.Perm (Fin 1755))) = hatF := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxA, hxC⟩ := mem_inf.1 hx
      have hxz : x ∈ titsA ⊓ centralizer {titsZ} :=
        mem_inf.2 ⟨hxA, mem_centralizer_singleton_iff.2
          (mem_centralizer_iff.1 hxC _ titsZ_mem_hatE).symm⟩
      rw [centralizer_titsZ_eq] at hxz
      exact mem_inf.2 ⟨twoF4H_centralizer_hatE_le (mem_inf.2 ⟨hxz, hxC⟩), hxC⟩
    · intro x hx
      obtain ⟨hxP, hxC⟩ := mem_inf.1 hx
      exact mem_inf.2 ⟨twoF4P_le_titsA hxP, hxC⟩
  refine ⟨hAF, ?_, by omega, hFD, ?_, fun a ha => ?_⟩
  · apply le_antisymm
    · intro x hx
      obtain ⟨hxD, hxC⟩ := mem_inf.1 hx
      rw [← hFD]
      exact mem_inf.2 ⟨hAF ▸ mem_inf.2 ⟨titsD_le_titsA hxD, hxC⟩, hxD⟩
    · intro x hx
      exact mem_inf.2 ⟨hED hx, mem_centralizer_iff.2 fun e he => hEc e he x hx⟩
  · intro a ha b hb
    have hcomm : ∀ {u v : Equiv.Perm (Fin 1755)}, u ∈ hatE → v ∈ hatF → u * v = v * u :=
      fun hu hv => (mem_centralizer_iff.1 (mem_inf.1 hv).2 _ hu)
    by_cases haD : a ∈ titsD
    · exact hcomm (hFD ▸ mem_inf.2 ⟨ha, haD⟩) hb
    by_cases hbD : b ∈ titsD
    · exact (hcomm (hFD ▸ mem_inf.2 ⟨hb, hbD⟩) ha).symm
    have hPA := twoF4P_le_titsA
    have hab : a * b⁻¹ ∈ hatE := hFD ▸ mem_inf.2 ⟨mul_mem ha (inv_mem hb),
      mul_inv_mem_titsD (hPA (mem_inf.1 ha).1) (hPA (mem_inf.1 hb).1) haD hbD⟩
    calc a * b = (a * b⁻¹) * b * b := by group
      _ = b * (a * b⁻¹) * b := by rw [hcomm hab hb]
      _ = b * a := by group
  · rw [← hFD]
    exact mem_inf.2 ⟨mul_mem ha ha, mul_self_mem_titsD (twoF4P_le_titsA (mem_inf.1 ha).1)⟩

end CFSG.LocalAnalysis.EvenBN.Tits.Model
