module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuGoldExcl
import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuX17Odd
import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuGold
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuCenter
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuTrans

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuQ

namespace RuQCode

theorem fix_two_check : (glList.all fun r => (List.finRange 8).all fun s =>
    (List.finRange 8).all fun t => s == 0 || t == 0 || s == t || linApply r s != s ||
      linApply r t != t ||
        (List.finRange 8).all fun u => linApply r (linApply r u) == u) = true := by
  decide +kernel

theorem linApply_linApply_of_fix {r : Lin8} (hr : r ∈ glList) {s t : Fin 8} (hs : s ≠ 0)
    (ht : t ≠ 0) (hst : s ≠ t) (hrs : linApply r s = s) (hrt : linApply r t = t) (u : Fin 8) :
    linApply r (linApply r u) = u := by
  have h := fix_two_check
  simp only [List.all_eq_true, List.mem_finRange, forall_true_left, Bool.or_eq_true,
    beq_iff_eq, bne_iff_ne, ne_eq] at h
  rcases h r hr s t with (((((h | h) | h) | h) | h) | h)
  · exact absurd h hs
  · exact absurd h ht
  · exact absurd h hst
  · exact absurd hrs h
  · exact absurd hrt h
  · exact h u

end RuQCode

variable {G : Type} [Group G] [Finite G]

theorem centralizer_le_normalizer_of_stronglyClosed
    (hG : GoldExcl.GoldschmidtComponents) {f : G} (hf1 : f ≠ 1)
    (hO : ∀ D : Subgroup G, D ≤ centralizer ({f} : Set G) → ¬ 2 ∣ Nat.card D →
      centralizer ({f} : Set G) ≤ normalizer (D : Set G) → D = ⊥)
    {S A : Subgroup G} (hS : IsSylowOf 2 S ⊤) (hSH : S ≤ centralizer ({f} : Set G))
    (hAS : A ≤ S) (hAel : IsElemAbelian 2 A) (hSA : S ≤ normalizer (A : Set G)) (hfA : f ∈ A)
    (hZS : S ⊓ centralizer (S : Set G) = zpowers f) (hcard : Nat.card A = 8 ∨ Nat.card A = 32)
    (hC : ∀ a ∈ A, a ∉ zpowers f →
      IsPGroup 2 (centralizer ({f} : Set G) ⊓ centralizer ({a} : Set G) : Subgroup G))
    (hcl : ∀ a ∈ A, ∀ h ∈ centralizer ({f} : Set G), h⁻¹ * a * h ∈ S → h⁻¹ * a * h ∈ A) :
    centralizer ({f} : Set G) ≤ normalizer (A : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := centralizer ({f} : Set G) with hH
  have hfH : f ∈ H := mem_centralizer_singleton_iff.mpr rfl
  have hAH : A ≤ H := hAS.trans hSH
  obtain ⟨Q, hQ⟩ := (hS.of_le hSH le_top).exists_sylow_eq_subgroupOf
  set A' : Subgroup H := A.subgroupOf H with hA'
  set f' : H := ⟨f, hfH⟩ with hf'
  have hmemQ : ∀ x : H, x ∈ (Q : Subgroup H) ↔ (x : G) ∈ S := fun x => by
    rw [hQ, mem_subgroupOf]
  have hO' : goldschmidtOddCore H = ⊥ := by
    rw [eq_bot_iff]
    refine sSup_le fun N hN => ?_
    obtain ⟨hNn, hodd⟩ := hN
    have hNH : (N.map H.subtype).subgroupOf H = N :=
      comap_map_eq_self_of_injective H.subtype_injective N
    have hnorm : H ≤ normalizer ((N.map H.subtype : Subgroup G) : Set G) := by
      have h1 : ((N.map H.subtype).subgroupOf H).Normal := by rw [hNH]; exact hNn
      exact (normal_subgroupOf_iff_le_normalizer (map_subtype_le N)).mp h1
    have h1 := hO (N.map H.subtype) (map_subtype_le N) (by
      rw [card_map_of_injective H.subtype_injective]
      exact fun h2 => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)) hnorm
    intro x hx
    have h2 : (x : G) ∈ N.map H.subtype := ⟨x, hx, rfl⟩
    rw [h1, mem_bot] at h2
    exact mem_bot.mpr (Subtype.ext h2)
  have hA'Q : A' ≤ (Q : Subgroup H) := fun x hx =>
    (hmemQ x).mpr (hAS (mem_subgroupOf.mp hx))
  have hA'ab : IsMulCommutative A' := CFSG.Goldschmidt.isMulCommutative_subgroupOf hAel.1 H
  have hA'2 : ∀ a ∈ A', a ^ 2 = 1 := fun a ha =>
    Subtype.ext (by simpa using hAel.2 _ (mem_subgroupOf.mp ha))
  have hQA : (Q : Subgroup H) ≤ normalizer (A' : Set H) := by
    intro q hq
    rw [mem_normalizer_iff]
    intro x
    have h1 := mem_normalizer_iff.mp (hSA ((hmemQ q).mp hq)) x
    rw [mem_subgroupOf, mem_subgroupOf, coe_mul, coe_mul, coe_inv]
    exact h1
  have hf'A : f' ∈ A' := mem_subgroupOf.mpr hfA
  have hf'1 : f' ≠ 1 := fun h => hf1 (congrArg Subtype.val h)
  have hf'c : ∀ h : H, h * f' = f' * h := fun h =>
    Subtype.ext (mem_centralizer_singleton_iff.mp h.2)
  have hmemZ : ∀ x : H, x ∈ zpowers f' ↔ (x : G) ∈ zpowers f := by
    intro x
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨n, by simp [hf']⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, Subtype.ext (by simpa [hf'] using hn)⟩
  have hZS' : (Q : Subgroup H) ⊓ centralizer ((Q : Subgroup H) : Set H) = zpowers f' := by
    ext x
    rw [mem_inf, hmemZ, ← hZS, mem_inf, hmemQ, mem_centralizer_iff, mem_centralizer_iff]
    refine and_congr_right fun _ => ⟨fun h s hs => ?_, fun h s hs => ?_⟩
    · have := h ⟨s, hSH hs⟩ ((hmemQ _).mpr hs)
      exact congrArg Subtype.val this
    · exact Subtype.ext (h (s : G) ((hmemQ s).mp hs))
  have hcard' : Nat.card A' = 8 ∨ Nat.card A' = 32 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hAH).toEquiv]
    exact hcard
  have hC' : ∀ a ∈ A', a ∉ zpowers f' → IsPGroup 2 (centralizer ({a} : Set H)) := by
    intro a ha haf
    have h1 := hC (a : G) (mem_subgroupOf.mp ha) (fun h => haf ((hmemZ a).mpr h))
    intro g
    obtain ⟨k, hk⟩ := h1 ⟨((g : H) : G), (g : H).2, mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp g.2))⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hk
    simpa using this
  have hcl' : fusionStronglyClosed (A' : Set H) (Q : Subgroup H) := by
    intro a ha g hg
    have h1 := hcl (a : G) (mem_subgroupOf.mp ha) g g.2 (by simpa using (hmemQ _).mp hg)
    exact mem_subgroupOf.mpr (by simpa using h1)
  have hn := GoldExcl.normal_of_stronglyClosed hG hO' Q hA'Q hA'ab hA'2 hQA hf'A hf'1 hf'c hZS'
    hcard' hC' hcl'
  intro h hh
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have h1 := hn.conj_mem ⟨x, hAH hx⟩ (mem_subgroupOf.mpr hx) ⟨h, hh⟩
    simpa using mem_subgroupOf.mp h1
  · intro hx
    have hxH : x ∈ H := by
      have h1 := mul_mem (mul_mem (inv_mem hh) (hAH hx)) hh
      simpa [mul_assoc] using h1
    have h1 := hn.conj_mem ⟨h * x * h⁻¹, hAH hx⟩ (mem_subgroupOf.mpr hx) ⟨h, hh⟩⁻¹
    have h2 := mem_subgroupOf.mp h1
    simpa [mul_assoc] using h2

theorem goldschmidtComponents :
    GoldExcl.GoldschmidtComponents :=
  fun _ _ _ hO S _ hAS hAab hcl => stronglyClosed_components_or_normal hO S hAS hAab hcl

namespace Sec3.SzR

variable {L T R R₂ : Subgroup G} {y d : G}

theorem dempwolff217
    (hS : SzR G L T R 1 y d) (h34 : NoStronglyClosedAbelian G) (hR₂ : IsR₂ L T R R₂ d)
    (h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4)
    (hCV : centralizer (gmsV L T : Set G) = T)
    (hCe : ∀ e ∈ T ⊓ centralizer (L : Set G), e ≠ 1 →
      centralizer ({e} : Set G) = (T ⊓ centralizer (L : Set G)) ⊔ L)
    (hCL : ∀ a ∈ L, a ≠ 1 → a ^ 2 = 1 →
      IsPGroup 2 (L ⊓ centralizer ({a} : Set G) : Subgroup G))
    (hNS : ¬ IsSylowOf 2 R (normalizer (R : Set G)))
    (h216 : ∀ F₁ : Subgroup G, F₁ ≤ gmsA L T → Nat.card F₁ = 4 →
      normalizer (F₁ : Set G) ≤ normalizer (R : Set G))
    (hkinds : ∀ (μ : G → ℕ) (ν : G → Fin 8), MaskCoords L T R μ ν → ∀ f ∈ gmsA L T, f ≠ 1 →
      ∀ X : Subgroup G, (∀ x, x ∈ X ↔ x ∈ R ∧ μ x ∈ 0 :: RuQCode.ppOf (ν f)) →
      ∃ S : Subgroup G, IsSylowOf 2 S ⊤ ∧ R ≤ S ∧ S ≤ normalizer (R : Set G) ∧
        S ≤ centralizer ({f} : Set G) ∧ X ≤ S ∧
        ∀ f₁ ∈ gmsA L T, f₁ ≠ 1 → f₁ ≠ f →
          ∀ h ∈ centralizer ({f} : Set G), h * f₁ * h⁻¹ ∈ S → h * f₁ * h⁻¹ ∈ X) :
    ∀ (μ : G → ℕ) (ν : G → Fin 8), MaskCoords L T R μ ν → ∀ S : Subgroup G,
      IsSylowOf 2 S (normalizer (R : Set G)) → ∀ f ∈ gmsA L T, f ≠ 1 →
      S ⊓ centralizer (S : Set G) = zpowers f → ∀ X : Subgroup G,
      (∀ x, x ∈ X ↔ x ∈ R ∧ μ x ∈ 0 :: RuQCode.ppOf (ν f)) →
      centralizer ({f} : Set G) ≤ normalizer (gmsA L T : Set G) ∨
        centralizer ({f} : Set G) ≤ normalizer (X : Set G) := by
  intro μ ν hM _ _ f hfA hf1 _ X hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := centralizer ({f} : Set G) with hH
  obtain ⟨hAel, hA8⟩ := hS.isElemAbelian_gmsA_and_card
  have hRp : IsPGroup 2 R := hS.isR.isPGroup
  have hNC := normalizer_inf_centralizer_eq hS h34 hR₂ h4 hCV
  have hidx := relIndex_normalizer_eq hS h34 hR₂ h4 hCV hNS
  have hAR : gmsA L T ≤ R := gmsA_le_T.trans hS.T_le
  have hAX : gmsA L T ≤ X := hM.gmsA_le_plane hX
  have hXel := hM.isElemAbelian_plane hX
  have hX32 := hM.card_plane hX hfA hf1
  have hf2 : f ^ 2 = 1 := hAel.2 f hfA
  have hof : orderOf f = 2 := orderOf_eq_prime hf2 hf1
  have hzf : ∀ z ∈ zpowers f, ∀ h ∈ H, h⁻¹ * z * h = z := by
    rintro _ ⟨n, rfl⟩ h hh
    have h1 : Commute h (f ^ n) := (Commute.zpow_right (mem_centralizer_singleton_iff.mp hh) n)
    rw [mul_assoc, ← h1.eq]
    group
  obtain ⟨S, hSsyl, hRS, hSN, hSH, hXS, hkind⟩ := hkinds μ ν hM f hfA hf1 X hX
  have hZ : S ⊓ centralizer (S : Set G) = zpowers f := by
    obtain ⟨f', hf'A, hf'1, hZf'⟩ :=
      exists_center_eq hS h34 hR₂ h4 hCV hCe hCL hNS (hSsyl.of_le hSN le_top)
    have hfZ : f ∈ S ⊓ centralizer (S : Set G) :=
      ⟨hRS (hAR hfA), mem_centralizer_iff.mpr fun s hs => mem_centralizer_singleton_iff.mp (hSH hs)⟩
    rw [hZf'] at hfZ ⊢
    have hle : zpowers f ≤ zpowers f' := zpowers_le.mpr hfZ
    refine (eq_of_le_of_card_ge hle ?_).symm
    rw [Nat.card_zpowers, Nat.card_zpowers, hof, orderOf_eq_prime (hAel.2 f' hf'A) hf'1]
  have hO : ∀ D : Subgroup G, D ≤ H → ¬ 2 ∣ Nat.card D → H ≤ normalizer (D : Set G) → D = ⊥ := by
    intro D hDH hDodd hHD
    refine eq_bot_of_odd_of_le_centralizer hS h4 hCe hCL (F₁ := zpowers f)
      (zpowers_le.mpr hfA) (by simpa using hf1) ?_ hDodd ?_
    · rw [zpowers_eq_closure, centralizer_closure]
      exact hDH
    · intro e he
      refine hHD (mem_centralizer_singleton_iff.mpr ?_)
      exact (mem_centralizer_iff.mp he.2 f (hfA.1.2)).symm
  have hSA : S ≤ normalizer (gmsA L T : Set G) := fun s hs =>
    mem_normalizer_fintype fun b hb => hM.normA s (hSN hs) b hb
  have hSX : S ≤ normalizer (X : Set G) := fun s hs =>
    hM.mem_normalizer_plane hX (hSN hs) (by rw [mem_centralizer_singleton_iff.mp (hSH hs)]; group)
      hfA
  obtain ⟨f₁, hf₁A, hf₁f⟩ : ∃ f₁ ∈ gmsA L T, f₁ ∉ zpowers f := by
    by_contra h
    push Not at h
    have h1 := card_le_of_le (show gmsA L T ≤ zpowers f from h)
    rw [Nat.card_zpowers, hof, hA8] at h1
    omega
  have hf₁1 : f₁ ≠ 1 := fun h => hf₁f (h ▸ one_mem _)
  have hf₁ne : f₁ ≠ f := fun h => hf₁f (h ▸ mem_zpowers f)
  have hne : ∀ a ∈ gmsA L T, a ∉ zpowers f → a ≠ 1 ∧ a ≠ f := fun a _ haf =>
    ⟨fun h => haf (h ▸ one_mem _), fun h => haf (h ▸ mem_zpowers f)⟩
  have htrA : ∀ a ∈ gmsA L T, a ∉ zpowers f → ∃ k ∈ H, a = k * f₁ * k⁻¹ := by
    intro a ha haf
    obtain ⟨g, -, hgf, hga⟩ := hM.exists_conj_eq_of_mem_gmsA hNC hidx hfA hf1 hf₁A hf₁1 hf₁ne
      ha (hne a ha haf).1 (hne a ha haf).2
    refine ⟨g, mem_centralizer_singleton_iff.mpr ?_, hga.symm⟩
    calc g * f = g * f * g⁻¹ * g := by group
      _ = f * g := by rw [hgf]
  have hCA : ∀ a ∈ gmsA L T, a ∉ zpowers f → IsPGroup 2 (H ⊓ centralizer ({a} : Set G) :
      Subgroup G) := by
    intro a ha haf
    set F₁ : Subgroup G := zpowers f ⊔ zpowers a with hF₁
    have hF₁A : F₁ ≤ gmsA L T := sup_le (zpowers_le.mpr hfA) (zpowers_le.mpr ha)
    have hF₁4 : Nat.card F₁ = 4 := by
      have hcomm : zpowers a ≤ normalizer ((zpowers f : Subgroup G) : Set G) := by
        refine zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ ?_)
        exact mem_centralizer_iff.mpr fun z hz => by
          obtain ⟨n, rfl⟩ := hz
          exact (Commute.zpow_left (show Commute f a from congrArg Subtype.val
            (hAel.1.is_comm.comm ⟨f, hfA⟩ ⟨a, ha⟩)) n).eq
      have h1 := CFSG.Walter.W67.card_sup_mul_card_inf_of_le_normalizer hcomm
      have hinf : zpowers f ⊓ zpowers a = ⊥ := by
        rw [eq_bot_iff]
        intro z hz
        obtain ⟨hzf, hza⟩ := mem_inf.mp hz
        by_contra hz1
        rw [mem_bot] at hz1
        obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hzf
        have hmod : f ^ n = f ^ (n % 2) := by
          have h2 := zpow_mod_orderOf f n
          rw [hof] at h2
          exact_mod_cast h2.symm
        rcases Int.emod_two_eq_zero_or_one n with h0 | h0
        · exact hz1 (by rw [hmod, h0, zpow_zero])
        · rw [hmod, h0, zpow_one] at hza
          obtain ⟨m, hm⟩ := mem_zpowers_iff.mp hza
          have hoa : orderOf a = 2 := orderOf_eq_prime (hAel.2 a ha) (hne a ha haf).1
          have hmod' : a ^ m = a ^ (m % 2) := by
            have h2 := zpow_mod_orderOf a m
            rw [hoa] at h2
            exact_mod_cast h2.symm
          rcases Int.emod_two_eq_zero_or_one m with h0' | h0'
          · rw [hmod', h0', zpow_zero] at hm
            exact hf1 hm.symm
          · rw [hmod', h0', zpow_one] at hm
            exact (hne a ha haf).2 hm
      rw [hinf, card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, hof,
        orderOf_eq_prime (hAel.2 a ha) (hne a ha haf).1] at h1
      exact h1
    have hle : H ⊓ centralizer ({a} : Set G) ≤ normalizer (R : Set G) := by
      refine le_trans ?_ (h216 F₁ hF₁A hF₁4)
      intro g hg
      refine Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun z hz => ?_)
      have hFg : F₁ ≤ centralizer ({g} : Set G) := sup_le
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
          (mem_centralizer_singleton_iff.mp (mem_inf.mp hg).1).symm))
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
          (mem_centralizer_singleton_iff.mp (mem_inf.mp hg).2).symm))
      exact mem_centralizer_singleton_iff.mp (hFg hz)
    have hνf : ν f ≠ 0 := fun h => hf1 (hM.ν_inj f hfA h)
    have hνa : ν a ≠ 0 := fun h => (hne a ha haf).1 (hM.ν_inj a ha h)
    have hνfa : ν f ≠ ν a := fun h => (hne a ha haf).2 (hM.eq_of_ν_eq ha hfA h.symm)
    intro g
    have hgN := hle g.2
    obtain ⟨r, hr, hrA, -⟩ := hM.act g hgN
    have hgf : (g : G) * f * (g : G)⁻¹ = f := by
      rw [mem_centralizer_singleton_iff.mp (mem_inf.mp g.2).1]
      group
    have hga : (g : G) * a * (g : G)⁻¹ = a := by
      rw [mem_centralizer_singleton_iff.mp (mem_inf.mp g.2).2]
      group
    have hrf : linApply r (ν f) = ν f := by rw [← hrA f hfA, hgf]
    have hra : linApply r (ν a) = ν a := by rw [← hrA a ha, hga]
    have hrr := RuQCode.linApply_linApply_of_fix hr hνf hνa hνfa hrf hra
    have hg2 : (g : G) ^ 2 ∈ R := by
      rw [← hNC]
      refine mem_inf.mpr ⟨pow_mem hgN 2, mem_centralizer_iff.mpr fun b hb => ?_⟩
      have hb1 := hM.normA g hgN b hb
      have h1 : (g : G) ^ 2 * b * ((g : G) ^ 2)⁻¹ = b := by
        refine hM.eq_of_ν_eq (hM.normA _ (pow_mem hgN 2) b hb) hb ?_
        rw [show (g : G) ^ 2 * b * ((g : G) ^ 2)⁻¹ = g * (g * b * (g : G)⁻¹) * (g : G)⁻¹ by
          rw [sq]; group, hrA _ hb1, hrA b hb, hrr]
      calc b * (g : G) ^ 2 = (g : G) ^ 2 * b * ((g : G) ^ 2)⁻¹ * (g : G) ^ 2 := by rw [h1]
        _ = (g : G) ^ 2 * b := by group
    obtain ⟨k, hk⟩ := hRp ⟨(g : G) ^ 2, hg2⟩
    refine ⟨k + 1, Subtype.ext ?_⟩
    have h1 : ((g : G) ^ 2) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [coe_pow, coe_one, pow_succ', pow_mul]
    exact h1
  have hCconj : ∀ k ∈ H, IsPGroup 2 (H ⊓ centralizer ({k * f₁ * k⁻¹} : Set G) : Subgroup G) := by
    intro k hk
    refine (IsPGroup.map (hCA f₁ hf₁A hf₁f) (MulAut.conj k).toMonoidHom).to_le ?_
    intro g hg
    have hgH := (mem_inf.mp hg).1
    have hgc := mem_centralizer_singleton_iff.mp (mem_inf.mp hg).2
    have hmem : k⁻¹ * g * k ∈ H ⊓ centralizer ({f₁} : Set G) := by
      refine mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem hk) hgH) hk,
        mem_centralizer_singleton_iff.mpr ?_⟩
      calc k⁻¹ * g * k * f₁ = k⁻¹ * (g * (k * f₁ * k⁻¹)) * k := by group
        _ = k⁻¹ * ((k * f₁ * k⁻¹) * g) * k := by rw [hgc]
        _ = f₁ * (k⁻¹ * g * k) := by group
    refine ⟨k⁻¹ * g * k, hmem, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hkf : ∀ k ∈ H, ∀ h ∈ H, h⁻¹ * (k * f₁ * k⁻¹) * h ∈ S →
      h⁻¹ * (k * f₁ * k⁻¹) * h ∈ X := by
    intro k hk h hh hS'
    have e : h⁻¹ * (k * f₁ * k⁻¹) * h = (h⁻¹ * k) * f₁ * (h⁻¹ * k)⁻¹ := by group
    rw [e] at hS' ⊢
    exact hkind f₁ hf₁A hf₁1 hf₁ne _ (mul_mem (inv_mem hh) hk) hS'
  by_cases hcase : ∃ k ∈ H, k * f₁ * k⁻¹ ∈ X ∧ k * f₁ * k⁻¹ ∉ gmsA L T
  ·
    right
    obtain ⟨k₀, hk₀H, hk₀X, hk₀A⟩ := hcase
    have htrX : ∀ x ∈ X, x ∉ zpowers f → ∃ k ∈ H, x = k * f₁ * k⁻¹ := by
      intro x hx hxf
      by_cases hxA : x ∈ gmsA L T
      · exact htrA x hxA hxf
      · obtain ⟨g, -, hgf, hgx⟩ :=
          hM.exists_conj_eq_of_not_mem hNC hidx hfA hf1 hX hk₀X hk₀A hx hxA
        have hgH : g ∈ H := mem_centralizer_singleton_iff.mpr (by
          calc g * f = g * f * g⁻¹ * g := by group
            _ = f * g := by rw [hgf])
        refine ⟨g * k₀, mul_mem hgH hk₀H, ?_⟩
        rw [← hgx]
        group
    have hCX : ∀ x ∈ X, x ∉ zpowers f →
        IsPGroup 2 (H ⊓ centralizer ({x} : Set G) : Subgroup G) := by
      intro x hx hxf
      obtain ⟨k, hk, rfl⟩ := htrX x hx hxf
      exact hCconj k hk
    have hcl : ∀ a ∈ X, ∀ h ∈ H, h⁻¹ * a * h ∈ S → h⁻¹ * a * h ∈ X := by
      intro a ha h hh haS
      by_cases haf : a ∈ zpowers f
      · rw [hzf a haf h hh]
        exact ha
      · obtain ⟨k, hk, rfl⟩ := htrX a ha haf
        exact hkf k hk h hh haS
    exact centralizer_le_normalizer_of_stronglyClosed goldschmidtComponents hf1 hO hSsyl hSH hXS
      hXel hSX (hAX hfA) hZ (Or.inr hX32) hCX hcl
  ·
    left
    push Not at hcase
    have hcl : ∀ a ∈ gmsA L T, ∀ h ∈ H, h⁻¹ * a * h ∈ S → h⁻¹ * a * h ∈ gmsA L T := by
      intro a ha h hh haS
      by_cases haf : a ∈ zpowers f
      · rw [hzf a haf h hh]
        exact ha
      · obtain ⟨k, hk, rfl⟩ := htrA a ha haf
        have h1 := hkf k hk h hh haS
        have e : h⁻¹ * (k * f₁ * k⁻¹) * h = (h⁻¹ * k) * f₁ * (h⁻¹ * k)⁻¹ := by group
        rw [e] at h1 ⊢
        exact hcase _ (mul_mem (inv_mem hh) hk) h1
    exact centralizer_le_normalizer_of_stronglyClosed goldschmidtComponents hf1 hO hSsyl hSH
      (hAR.trans hRS) hAel
      hSA hfA hZ (Or.inl hA8) hCA hcl

end Sec3.SzR

end CFSG.ComponentClassification.GMS78
