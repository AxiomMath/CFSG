module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem20TrA
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL2

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

namespace Lem20T

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}

theorem inf_centralizer_eq_bot_F4 (h1222 : Stmt12_2_2_F4) (hH : Hyp1223 G T L V)
    [IsMulCommutative ↥V] {A : Subgroup ↥V} (hA : A.index = 2)
    (hle : transvAxis A ≤
      autOn (Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V : Set G)) V) :
    V ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  classical
  obtain ⟨-, -, hall⟩ := ((h1222 G T hH.simple hH.nonabelian hH.qtke hH.sylow).resolve_left
    hH.notAlt) L hH.maximal hH.faithful hH.quasisimple
  obtain ⟨⟨-, hTV, hred, -⟩, -, -, -, -⟩ := hall V hH.irrPlus
  set Z₀ := V ⊓ Subgroup.centralizer (L : Set G) with hZ₀
  have hV2' : ∀ v : ↥V, v * v = 1 := fun v => by
    rw [← pow_two]
    exact sq_eq_one_of_hyp1223 hH hred v
  have hLV := le_normalizer_of_hyp1223 hH
  have hVZ : ¬ V ≤ Z₀ := not_le_of_gt hH.irrPlus.2.2.2.2.1

  have htM : ∀ {c : ↥V} (hc : c ∈ A), MulAutTwo.transv hV2' hA hc ∈
      autOn (Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V : Set G)) V :=
    fun hc => hle ⟨fun _ ha => MulAutTwo.transv_of_mem hV2' hA hc ha,
      MulAutTwo.transv_mul_inv_mem hV2' hA hc⟩

  have hmZ : ∀ m ∈ Subgroup.normalizer (L : Set G), m ∈ Subgroup.normalizer (V : Set G) →
      ∀ y ∈ Z₀, m * y * m⁻¹ ∈ Z₀ := fun m hmL hmV y hy =>
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hmV, B6.le_normalizer_centralizer le_rfl hmL⟩) y).mp hy
  by_contra hZ1
  obtain ⟨z, hz, hz1⟩ : ∃ z ∈ Z₀, z ≠ 1 := by
    by_contra h0
    push Not at h0
    exact hZ1 (eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr (h0 x hx))
  by_cases hZA : ∀ y (hy : y ∈ Z₀), (⟨y, hy.1⟩ : ↥V) ∈ A
  ·
    have hzA : (⟨z, hz.1⟩ : ↥V) ∈ A := hZA z hz
    obtain ⟨m, hmL, hmV, hm⟩ := exists_conj_of_mem (htM hzA)
    have hF1 : ∀ w ∈ V, m * w * m⁻¹ * w⁻¹ ∈ Z₀ := by
      intro w hw
      rw [← hm ⟨w, hw⟩]
      by_cases hwA : (⟨w, hw⟩ : ↥V) ∈ A
      · rw [MulAutTwo.transv_of_mem hV2' hA hzA hwA]
        simp [Z₀.one_mem]
      · rw [MulAutTwo.transv_of_not_mem hV2' hA hzA hwA]
        have e : (((⟨w, hw⟩ : ↥V) * ⟨z, hz.1⟩ : ↥V) : G) * w⁻¹ =
            (((⟨w, hw⟩ : ↥V) * ⟨z, hz.1⟩ * (⟨w, hw⟩ : ↥V)⁻¹ : ↥V) : G) := by
          push_cast
          rfl
        rw [e, mul_comm (⟨w, hw⟩ : ↥V) ⟨z, hz.1⟩, mul_inv_cancel_right]
        exact hz
    have hF2 : ∀ a (ha : a ∈ V), (⟨a, ha⟩ : ↥V) ∈ A → m * a * m⁻¹ = a := by
      intro a ha haA
      rw [← hm ⟨a, ha⟩, MulAutTwo.transv_of_mem hV2' hA hzA haA]
    have hF1' : ∀ w ∈ V, m⁻¹ * w * m * w⁻¹ ∈ Z₀ := by
      intro w hw
      have hu : m⁻¹ * w * m ∈ V := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hmV) w).mp hw
        simpa using this
      have h1 := hF1 _ hu
      have e : m * (m⁻¹ * w * m) * m⁻¹ * (m⁻¹ * w * m)⁻¹ = (m⁻¹ * w * m * w⁻¹)⁻¹ := by group
      rw [e] at h1
      simpa using Z₀.inv_mem h1
    have hcomm : ∀ l ∈ L, m * l * m⁻¹ * l⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
      intro l hl
      have hmlL : m * l * m⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hmL l).mp hl
      refine mem_centralizer_of_stab hH hTV hred
        (Subgroup.mem_sup_left (L.mul_mem hmlL (L.inv_mem hl))) (fun v hv => ?_)
        (fun y hy => ?_)
      · have hv₁ : l⁻¹ * v * l ∈ V := by
          have := (Subgroup.mem_normalizer_iff.mp (hLV (L.inv_mem hl)) v).mp hv
          simpa using this
        set y₁ := m⁻¹ * (l⁻¹ * v * l) * m * (l⁻¹ * v * l)⁻¹ with hy₁
        have hy₁Z : y₁ ∈ Z₀ := hF1' _ hv₁
        have e : m⁻¹ * (l⁻¹ * v * l) * m = y₁ * (l⁻¹ * v * l) := by rw [hy₁]; group
        have hly : l * y₁ * l⁻¹ = y₁ := by
          rw [(Subgroup.mem_centralizer_iff.mp hy₁Z.2) l hl]
          group
        have hmy : m * y₁ * m⁻¹ = y₁ := hF2 y₁ hy₁Z.1 (hZA y₁ hy₁Z)
        have e2 : m * l * m⁻¹ * l⁻¹ * v * (m * l * m⁻¹ * l⁻¹)⁻¹ * v⁻¹ =
            y₁ * (m * v * m⁻¹ * v⁻¹) := by
          calc m * l * m⁻¹ * l⁻¹ * v * (m * l * m⁻¹ * l⁻¹)⁻¹ * v⁻¹ =
                m * (l * (m⁻¹ * (l⁻¹ * v * l) * m) * l⁻¹) * m⁻¹ * v⁻¹ := by group
            _ = m * (l * (y₁ * (l⁻¹ * v * l)) * l⁻¹) * m⁻¹ * v⁻¹ := by rw [e]
            _ = (m * (l * y₁ * l⁻¹) * m⁻¹) * (m * v * m⁻¹ * v⁻¹) := by group
            _ = y₁ * (m * v * m⁻¹ * v⁻¹) := by rw [hly, hmy]
        rw [e2]
        exact Z₀.mul_mem hy₁Z (hF1 v hv)
      · have hly : ∀ g ∈ L, g * y * g⁻¹ = y := fun g hg => by
          rw [(Subgroup.mem_centralizer_iff.mp hy.2) g hg]
          group
        have hmy : m * y * m⁻¹ = y := hF2 y hy.1 (hZA y hy)
        have hmy' : m⁻¹ * y * m = y := by
          calc m⁻¹ * y * m = m⁻¹ * (m * y * m⁻¹) * m := by rw [hmy]
            _ = y := by group
        calc m * l * m⁻¹ * l⁻¹ * y * (m * l * m⁻¹ * l⁻¹)⁻¹ =
              m * (l * (m⁻¹ * (l⁻¹ * y * l⁻¹⁻¹) * m) * l⁻¹) * m⁻¹ := by group
          _ = y := by rw [hly _ (L.inv_mem hl), hmy', hly l hl, hmy]

    have hAL : ∀ l ∈ L, ∀ a (ha : a ∈ V), (⟨a, ha⟩ : ↥V) ∈ A →
        ∀ h' : l * a * l⁻¹ ∈ V, (⟨l * a * l⁻¹, h'⟩ : ↥V) ∈ A := by
      intro l hl a ha haA h'
      by_contra hna
      have hx := hcomm l hl
      have hma : m⁻¹ * a * m = a := by
        calc m⁻¹ * a * m = m⁻¹ * (m * a * m⁻¹) * m := by rw [hF2 a ha haA]
          _ = a := by group
      have h1 : m * (l * a * l⁻¹) * m⁻¹ = l * a * l⁻¹ := by
        have hxv := (Subgroup.mem_centralizer_iff.mp hx) (l * a * l⁻¹) h'
        calc m * (l * a * l⁻¹) * m⁻¹ = m * (l * (m⁻¹ * a * m) * l⁻¹) * m⁻¹ := by rw [hma]
          _ = (m * l * m⁻¹ * l⁻¹) * (l * a * l⁻¹) * (m * l * m⁻¹ * l⁻¹)⁻¹ := by group
          _ = l * a * l⁻¹ := by rw [← hxv]; group
      have h2 := hm ⟨l * a * l⁻¹, h'⟩
      rw [MulAutTwo.transv_of_not_mem hV2' hA hzA hna, h1] at h2
      apply hz1
      have h3 : (l * a * l⁻¹) * z = l * a * l⁻¹ := h2
      calc z = (l * a * l⁻¹)⁻¹ * ((l * a * l⁻¹) * z) := by group
        _ = 1 := by rw [h3]; group
    have hLA : L ≤ Subgroup.normalizer ((A.map V.subtype : Subgroup G) : Set G) := by
      refine le_normalizer_map_of_invariant hLV fun σ hσ w hw => ?_
      obtain ⟨⟨l, hl⟩, rfl⟩ := (A4.mem_autOn_iff hLV).mp hσ
      exact hAL l hl w w.2 hw _
    have hZAm : Z₀ ≤ A.map V.subtype := fun y hy => ⟨⟨y, hy.1⟩, hZA y hy, rfl⟩
    rcases irreducible_of_hyp1223 hH _ hZAm (Subgroup.map_subtype_le A) hLA with h | h
    ·
      apply hVZ
      rw [← commutator_eq_of_hyp1223 hH, Subgroup.commutator_le]
      intro v hv l hl
      rw [commutatorElement_def, show Z₀ = A.map V.subtype from h.symm]
      have hlv : l * v⁻¹ * l⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp (hLV hl) v⁻¹).mp (V.inv_mem hv)
      have hiff : (⟨l * v⁻¹ * l⁻¹, hlv⟩ : ↥V) ∈ A ↔ (⟨v, hv⟩ : ↥V) ∈ A := by
        constructor
        · intro h1
          have e0 : l⁻¹ * (l * v⁻¹ * l⁻¹) * l⁻¹⁻¹ = v⁻¹ := by group
          have hmem : l⁻¹ * (l * v⁻¹ * l⁻¹) * l⁻¹⁻¹ ∈ V := by
            rw [e0]
            exact V.inv_mem hv
          have h2 := hAL l⁻¹ (L.inv_mem hl) _ hlv h1 hmem
          have e : (⟨l⁻¹ * (l * v⁻¹ * l⁻¹) * l⁻¹⁻¹, hmem⟩ : ↥V) = (⟨v, hv⟩ : ↥V)⁻¹ :=
            Subtype.ext e0
          rw [e] at h2
          simpa using A.inv_mem h2
        · intro h1
          exact hAL l hl _ (V.inv_mem hv) (A.inv_mem h1) hlv
      have hprod : (⟨v, hv⟩ : ↥V) * ⟨l * v⁻¹ * l⁻¹, hlv⟩ ∈ A :=
        (Subgroup.mul_mem_iff_of_index_two hA).mpr hiff.symm
      refine ⟨_, hprod, ?_⟩
      show v * (l * v⁻¹ * l⁻¹) = v * l * v⁻¹ * l⁻¹
      group
    ·
      have hAt : A = ⊤ := by
        rw [eq_top_iff]
        intro w _
        have hw : (w : G) ∈ A.map V.subtype := by rw [h]; exact w.2
        obtain ⟨w', hw'A, hw'e⟩ := hw
        rwa [show w' = w from Subtype.ext hw'e] at hw'A
      rw [hAt, Subgroup.index_top] at hA
      exact absurd hA (by norm_num)
  ·
    push Not at hZA
    obtain ⟨y, hy, hyA⟩ := hZA
    have hAZ : ∀ c ∈ A, (c : G) ∈ Z₀ := by
      intro c hc
      obtain ⟨m, hmL, hmV, hm⟩ := exists_conj_of_mem (htM hc)
      have h1 := hm ⟨y, hy.1⟩
      rw [MulAutTwo.transv_of_not_mem hV2' hA hc hyA] at h1
      have h2 : (((⟨y, hy.1⟩ : ↥V) * c : ↥V) : G) ∈ Z₀ := by
        rw [h1]
        exact hmZ m hmL hmV y hy
      have h3 : (c : G) = y⁻¹ * (((⟨y, hy.1⟩ : ↥V) * c : ↥V) : G) := by
        push_cast
        group
      rw [h3]
      exact Z₀.mul_mem (Z₀.inv_mem hy) h2
    apply hVZ
    intro v hv
    by_cases hvA : (⟨v, hv⟩ : ↥V) ∈ A
    · exact hAZ _ hvA
    · have h1 : (⟨v, hv⟩ : ↥V) * ⟨y, hy.1⟩ ∈ A :=
        (Subgroup.mul_mem_iff_of_index_two hA).mpr (iff_of_false hvA hyA)
      have h2 := hAZ _ h1
      have h3 : v = (((⟨v, hv⟩ : ↥V) * ⟨y, hy.1⟩ : ↥V) : G) * y⁻¹ := by
        push_cast
        group
      rw [h3]
      exact Z₀.mul_mem h2 (Z₀.inv_mem hy)

theorem autOn_eq_top_F4 (h1222 : Stmt12_2_2_F4) (hH : Hyp1223 G T L V)
    [IsMulCommutative ↥V] {A : Subgroup ↥V} (hA : A.index = 2) (hA4 : 4 ≤ Nat.card A)
    (hle : transvAxis A ≤
      autOn (Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V : Set G)) V) :
    autOn L V = ⊤ := by
  classical
  have hC := inf_centralizer_eq_bot_F4 h1222 hH hA hle
  obtain ⟨-, -, hall⟩ := ((h1222 G T hH.simple hH.nonabelian hH.qtke hH.sylow).resolve_left
    hH.notAlt) L hH.maximal hH.faithful hH.quasisimple
  obtain ⟨⟨-, -, hred, -⟩, -, -, -, -⟩ := hall V hH.irrPlus
  have hV2' : ∀ v : ↥V, v * v = 1 := fun v => by
    rw [← pow_two]
    exact sq_eq_one_of_hyp1223 hH hred v
  have hLV := le_normalizer_of_hyp1223 hH
  set M := autOn (Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V : Set G)) V with hM
  have hLM : autOn L V ≤ M := A4.autOn_mono (le_inf Subgroup.le_normalizer hLV)

  have hirr : ∀ U : Subgroup ↥V, (∀ h ∈ M, ∀ u ∈ U, h u ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    have hUL := le_normalizer_map_of_invariant hLV (W := U) fun h hh u hu => hU h (hLM hh) u hu
    have hCU : V ⊓ Subgroup.centralizer (L : Set G) ≤ U.map V.subtype := by
      rw [hC]
      exact bot_le
    rcases irreducible_of_hyp1223 hH _ hCU (Subgroup.map_subtype_le U) hUL with h | h
    · left
      rw [hC] at h
      rw [eq_bot_iff]
      intro u hu
      have : (u : G) ∈ U.map V.subtype := ⟨u, hu, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr (Subtype.ext this)
    · right
      rw [eq_top_iff]
      intro w _
      have hw : (w : G) ∈ U.map V.subtype := by rw [h]; exact w.2
      obtain ⟨w', hw'U, hw'e⟩ := hw
      rwa [show w' = w from Subtype.ext hw'e] at hw'U

  have hMtop : M = ⊤ := MulAutTwo.eq_top_of_transv hV2' M hirr A hA fun σ h1 h2 => hle ⟨h1, h2⟩

  have hnorm : (autOn L V).Normal := by
    refine ⟨fun σ hσ g => ?_⟩
    have hg : g ∈ M := by rw [hMtop]; trivial
    obtain ⟨m, hmL, -, hm⟩ := exists_conj_of_mem hg
    obtain ⟨⟨l, hl⟩, rfl⟩ := (A4.mem_autOn_iff hLV).mp hσ
    have hml : m * l * m⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hmL l).mp hl
    have hginv : ∀ v : ↥V, ((g⁻¹ v : ↥V) : G) = m⁻¹ * v * m := by
      intro v
      have h1 := hm (g⁻¹ v)
      rw [MulAut.apply_inv_self] at h1
      calc ((g⁻¹ v : ↥V) : G) = m⁻¹ * (m * (g⁻¹ v : ↥V) * m⁻¹) * m := by group
        _ = m⁻¹ * v * m := by rw [← h1]
    refine (A4.mem_autOn_iff hLV).mpr ⟨⟨m * l * m⁻¹, hml⟩, ?_⟩
    refine MulEquiv.ext fun v => Subtype.ext ?_
    rw [MulAut.mul_apply, MulAut.mul_apply, hm, A4.actionOn_apply_coe, A4.actionOn_apply_coe,
      hginv]
    group

  have h8 : 8 ≤ Nat.card ↥V := by
    have := A.card_mul_index
    rw [hA] at this
    omega
  have hs := MulAutTwo.isSimpleGroup_mulAut hV2' h8
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (autOn L V) with h | h
  · exfalso
    apply not_le_centralizer_of_hyp1223 hH
    intro l hl
    have hmem : A4.actionOn V L hLV ⟨l, hl⟩ ∈ autOn L V := (A4.mem_autOn_iff hLV).mpr ⟨_, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact (A4.actionOn_eq_one_iff hLV _).mp hmem
  · exact h

end Lem20T

end CFSG.Quasithin.H13
