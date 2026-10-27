module

public import CFSG.GH74.Uniqueness.Section13B
public import CFSG.GH74.Uniqueness.Section13Count
public import CFSG.GH74.Uniqueness.Section132
public import CFSG.GH74.Uniqueness.Section133
public import CFSG.GH74.Uniqueness.Section134
public import CFSG.GH74.Uniqueness.Section134U

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

section Aux

omit [Finite X] in
theorem A6.exists_omega (Q : Subgroup X) (hQc : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) :
    ∃ E : Subgroup X, (E : Set X) = {y | y ∈ Q ∧ y * y = 1} := by
  refine ⟨{ carrier := {y | y ∈ Q ∧ y * y = 1}
            mul_mem' := fun {a b} ha hb => ⟨Q.mul_mem ha.1 hb.1, ?_⟩
            one_mem' := ⟨Q.one_mem, mul_one 1⟩
            inv_mem' := fun {a} ha => ⟨Q.inv_mem ha.1, by rw [← mul_inv_rev, ha.2, inv_one]⟩ }, rfl⟩
  have h1 := hQc b hb.1 a ha.1
  calc a * b * (a * b) = a * (b * a) * b := by group
    _ = a * (a * b) * b := by rw [h1]
    _ = (a * a) * (b * b) := by group
    _ = 1 := by rw [ha.2, hb.2, mul_one]

theorem A6.card_le_two_mul {G H : Type*} [Group G] [Group H] [Finite G] (f : G →* H)
    (K : Subgroup G) {a : G} (hker : ∀ y ∈ K, f y = 1 → y = 1 ∨ y = a) :
    Nat.card K ≤ 2 * Nat.card (K.map f) := by
  classical
  set g : ↥K →* H := f.comp K.subtype with hg
  have h1 : Nat.card g.ker * Nat.card g.range = Nat.card K := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have h2 : g.range = K.map f := by
    rw [hg, MonoidHom.range_comp, Subgroup.range_subtype]
  have h3 : Nat.card g.ker ≤ 2 := by
    have h4 : Nat.card g.ker ≤ Nat.card ↥({1, a} : Set G) := by
      refine Nat.card_le_card_of_injective (fun y => ⟨((y : ↥K) : G), ?_⟩) ?_
      · rcases hker _ (y : ↥K).2 (MonoidHom.mem_ker.mp y.2) with h | h
        · exact Or.inl h
        · exact Or.inr h
      · intro y z hyz
        have h6 := Subtype.ext_iff.mp hyz
        exact Subtype.ext (Subtype.ext h6)
    rw [Nat.card_coe_set_eq] at h4
    have h5 : ({1, a} : Set G).ncard ≤ 2 := by
      calc ({1, a} : Set G).ncard ≤ ({a} : Set G).ncard + 1 := Set.ncard_insert_le _ _
        _ = 2 := by rw [Set.ncard_singleton]
    omega
  rw [← h1, ← h2]
  exact Nat.mul_le_mul_right _ h3

end Aux

theorem A6.false_of_unitary
    (S : ZDSetup X Z M) (h12 : Sec12Results Z M) {c : Ctx12 Z M} {n : ℕ}
    (hL : LData c n 1)
    (hall : ∀ u ∈ c.D, orderOf u = 2 → c.L < cenHull Z u ∧ ∃ e, BenderSub Z M (cenHull Z u) n 3 e)
    {u₀ : X} (hu₀ : u₀ ∈ c.D) (hu₀2 : orderOf u₀ = 2) : False := by
  classical
  have hZ := S.invariant
  set 𝒢 : Set (Subgroup X) := {R | IsPGroup 2 R ∧ (∀ x ∈ R, ∀ y ∈ R, x * y = y * x) ∧
    ∃ x, x ∈ M ∧ x ∉ zHull Z M ∧ orderOf x = 2 ∧ R ≤ centralizer ({x} : Set X)} with h𝒢
  set r : Subgroup X → ℕ := fun R => ({x : X | x ∈ R ∧ x * x = 1} : Set X).ncard with hr
  have hbot : (⊥ : Subgroup X) ∈ 𝒢 :=
    ⟨IsPGroup.of_bot, fun x hx y hy => by
      rw [mem_bot] at hx hy
      rw [hx, hy], u₀, (mem_inf.mp hu₀).1, hL.sec126_not_mem_zHull S hu₀ hu₀2, hu₀2, bot_le⟩
  have : Finite (Subgroup X) := Finite.of_injective (fun H : Subgroup X => (H : Set X))
    SetLike.coe_injective
  have : Nonempty ↥𝒢 := ⟨⟨⊥, hbot⟩⟩
  obtain ⟨⟨Q₀, hQ₀⟩, hmax₀⟩ := Finite.exists_max
    (fun R : ↥𝒢 => r R.1 * (Nat.card X + 1) + Nat.card R.1)
  have hlex : ∀ R ∈ 𝒢, r R ≤ r Q₀ ∧ (r R = r Q₀ → Nat.card R ≤ Nat.card Q₀) := by
    intro R hR
    have h1 := hmax₀ ⟨R, hR⟩
    simp only at h1
    have hQX : Nat.card Q₀ ≤ Nat.card X := Subgroup.card_le_card_group (H := Q₀)
    have hle : r R ≤ r Q₀ := by
      by_contra hlt
      have h2 : (r Q₀ + 1) * (Nat.card X + 1) ≤ r R * (Nat.card X + 1) :=
        Nat.mul_le_mul_right _ (by omega)
      have h3 : (r Q₀ + 1) * (Nat.card X + 1) = r Q₀ * (Nat.card X + 1) + (Nat.card X + 1) := by
        ring
      linarith
    refine ⟨hle, fun heq => ?_⟩
    rw [heq] at h1
    exact Nat.le_of_add_le_add_left h1
  obtain ⟨hQ₀p, hQ₀c, x, hxM, hxMo, hx2, hQ₀x⟩ := hQ₀
  have hxZ : x ∉ Z := fun h => hxMo (subset_closure ⟨h, hxM⟩)
  obtain ⟨h1211a, -, h1211b⟩ := h12.l1211 c n 1 hL
  obtain ⟨u, hu, hu2, hxu⟩ := h1211b x hx2 (fun h => hxZ ((h1211a x hx2).mp h))
  obtain ⟨g, hg⟩ := isConj_iff.mp hxu
  set cg : X →* X := (MulAut.conj g).toMonoidHom with hcg
  have hcgv : ∀ w, cg w = g * w * g⁻¹ := fun w => by simp [hcg]
  have hcginj : Function.Injective cg := (MulAut.conj g).injective
  set Q : Subgroup X := Q₀.map cg with hQdef
  have hQu : Q ≤ centralizer ({u} : Set X) := by
    rintro _ ⟨q, hq, rfl⟩
    rw [mem_centralizer_singleton_iff, hcgv, ← hg]
    have h1 := mem_centralizer_singleton_iff.mp (hQ₀x hq)
    calc g * q * g⁻¹ * (g * x * g⁻¹) = g * (q * x) * g⁻¹ := by group
      _ = g * (x * q) * g⁻¹ := by rw [h1]
      _ = g * x * g⁻¹ * (g * q * g⁻¹) := by group
  have hQc : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hQ₀c a ha b hb]
  have hQp : IsPGroup 2 Q := hQ₀p.map cg
  have hrQ : r Q = r Q₀ := by
    have himg : cg '' {x : X | x ∈ Q₀ ∧ x * x = 1} = {x : X | x ∈ Q ∧ x * x = 1} := by
      ext y
      constructor
      · rintro ⟨w, ⟨hw, hww⟩, rfl⟩
        exact ⟨⟨w, hw, rfl⟩, by rw [← map_mul, hww, map_one]⟩
      · rintro ⟨⟨w, hw, rfl⟩, hww⟩
        refine ⟨w, ⟨hw, hcginj (by rw [map_mul, hww, map_one])⟩, rfl⟩
    rw [hr]
    simp only
    rw [← himg, Set.ncard_image_of_injective _ hcginj]
  have hQcard : Nat.card Q = Nat.card Q₀ := card_map_of_injective hcginj
  have hmax : ∀ R ∈ 𝒢, r R ≤ r Q ∧ (r R = r Q → Nat.card R ≤ Nat.card Q) := by
    intro R hR
    rw [hrQ, hQcard]
    exact hlex R hR
  obtain ⟨hLlt, e, hBu⟩ := hall u hu hu2
  have hLu : c.L ≤ cenHull Z u := hLlt.le
  have huM : u ∈ M := (mem_inf.mp hu).1
  obtain ⟨Tb, T, hDu⟩ := A6.exists_dict hBu
  obtain ⟨A, H, hA⟩ := A6.exists_aData S hL hDu hLu
  have hAu : A ≤ cenHull Z u := hA.le_H.trans hA.H_le_F
  have hA0 : ∃ a ∈ A, ∃ y ∈ cenHull Z u, a * y ≠ y * a := by
    obtain ⟨a, ha, haF, -, ha1⟩ := hA.exists_ne
    have hac : (⟨a, haF⟩ : ↥(cenHull Z u)) ∉ center ↥(cenHull Z u) := fun h =>
      ha1 ((QuotientGroup.eq_one_iff _).mpr h)
    rw [mem_center_iff] at hac
    push Not at hac
    obtain ⟨y, hy⟩ := hac
    exact ⟨a, ha, y, y.2, fun h => hy (Subtype.ext h.symm)⟩
  obtain ⟨e', hBA, hnotle, hun, hα2, hout, hfix⟩ :=
    A6.lemma132 S h12 hL hu hu2 hBu hAu hA.odd hA.comm_L hA0
  have hLA := A6.L_le_LA S c hA.comm_L
  obtain ⟨Vb, V, hDA⟩ := A6.exists_dict hBA
  obtain ⟨U, hUV, hUc, hUcard, hMU, hUsq, hUinv, -, hUH⟩ :=
    A6.exists_U S hL huM hDA hLA hun hα2 hout
  have hTU := A6.lemma134 S hL hDu hLu hA hDA hUV hUc hMU hUsq hUinv hUH
  have hTu : ∀ s ∈ T, u * s = s * u := fun s hs => mul_comm_of_mem_cenHull (hDu.le hs)
  obtain ⟨R, hRp, hRc, hRM, hOmega, hRcard, y, hyR, hyMo, hy2⟩ :=
    A6.exists_R S hL hDu hDA (hL.m_le.trans hLu) (hL.m_le.trans hLA) hTu hUV hUc hUcard hUsq
      hUinv hTU
  have hR𝒢 : R ∈ 𝒢 := ⟨hRp, hRc, y, hRM hyR, hyMo, hy2, fun z hz =>
    mem_centralizer_singleton_iff.mpr (hRc z hz y hyR)⟩
  obtain ⟨hrR, hRQ⟩ := hmax R hR𝒢
  set Lu := cenHull Z u with hLudef
  set N := normalizer (Lu : Set X) with hN
  have hCN : centralizer ({u} : Set X) ≤ N := fun w hw =>
    A6.mem_normalizer_zHull hZ (le_normalizer hw)
  have huN : u ∈ N := hCN (mem_centralizer_singleton_iff.mpr rfl)
  have hodd := A2.odd_card_center_of_benderSub hBu
  have hker : ∀ K : Subgroup X, K ≤ centralizer ({u} : Set X) →
      ∀ w ∈ K.subgroupOf N, A6.barHom Lu w = 1 → w = 1 ∨ w = ⟨u, huN⟩ := by
    intro K hK w hw hw1
    have hwc := A6.mem_centralizer_of_barHom_eq_one Lu (fun z hz => hZ.mul_self_eq_one hz)
      hBu.zhull hodd w (fun z _ hzF => by rw [hw1, MulAut.one_apply])
    have hwu : (w : X) * u = u * w := mem_centralizer_singleton_iff.mp (hK hw)
    rcases A6.lemma133 S hL hu2 hBu hLu hAu hBA hnotle hun hα2 hout hfix hwu
      (fun y hy => (mem_centralizer_iff.mp hwc y hy).symm) with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  obtain ⟨E, hE⟩ := A6.exists_omega Q hQc
  have hEQ : E ≤ Q := fun w hw => by
    have : w ∈ (E : Set X) := hw
    rw [hE] at this
    exact this.1
  have hEsq : ∀ w ∈ E, w * w = 1 := fun w hw => by
    have : w ∈ (E : Set X) := hw
    rw [hE] at this
    exact this.2
  have hrE : r Q = Nat.card E := by
    rw [hr]
    simp only
    rw [← hE, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe]
  set Eb : Subgroup (MulAut (↥Lu ⧸ center ↥Lu)) := (E.subgroupOf N).map (A6.barHom Lu) with hEb
  have hEbsq : ∀ σ ∈ Eb, σ * σ = 1 := by
    rintro _ ⟨w, hw, rfl⟩
    rw [← map_mul]
    have : w * w = 1 := Subtype.ext (hEsq _ hw)
    rw [this, map_one]
  have hEbcard := (hBu.bender.card_le_of_sq_eq_one_aut Eb hEbsq).1
  have hEcard : Nat.card E ≤ 2 * Nat.card Eb := by
    have h1 := A6.card_le_two_mul (A6.barHom Lu) (E.subgroupOf N)
      (hker E (hEQ.trans hQu))
    rwa [A6.card_subgroupOf ((hEQ.trans hQu).trans hCN)] at h1
  have hn2 : n = 2 := by
    have h1 : (2 ^ n) ^ 2 ≤ 2 * 2 ^ (n + 1) := by
      calc (2 ^ n) ^ 2 ≤ r R := hOmega
        _ ≤ r Q := hrR
        _ = Nat.card E := hrE
        _ ≤ 2 * Nat.card Eb := hEcard
        _ ≤ 2 * 2 ^ (n + 1) := Nat.mul_le_mul_left _ hEbcard
    have h2 : (2 : ℕ) ^ (n * 2) ≤ 2 ^ (n + 2) := by
      calc (2 : ℕ) ^ (n * 2) = (2 ^ n) ^ 2 := by rw [pow_mul]
        _ ≤ 2 * 2 ^ (n + 1) := h1
        _ = 2 ^ (n + 2) := by ring
    have h3 : n * 2 ≤ n + 2 := (Nat.pow_le_pow_iff_right (by norm_num)).mp h2
    have := hL.hn
    omega
  subst hn2
  have hrQ16 : r Q = 16 := by
    have h1 : 16 ≤ r Q := by
      calc 16 = (2 ^ 2) ^ 2 := by norm_num
        _ ≤ r R := hOmega
        _ ≤ r Q := hrR
    have h2 : r Q ≤ 16 := by
      calc r Q = Nat.card E := hrE
        _ ≤ 2 * Nat.card Eb := hEcard
        _ ≤ 2 * 2 ^ (2 + 1) := Nat.mul_le_mul_left _ hEbcard
        _ = 16 := by norm_num
    omega
  have hrR16 : r R = 16 := by
    have h1 : 16 ≤ r R := by
      calc 16 = (2 ^ 2) ^ 2 := by norm_num
        _ ≤ r R := hOmega
    omega
  have hQ64 : 64 ≤ Nat.card Q := by
    calc 64 = (2 ^ 2) ^ 3 := by norm_num
      _ ≤ Nat.card R := hRcard
      _ ≤ Nat.card Q := hRQ (by rw [hrR16, hrQ16])
  have hEb8 : 2 ^ 2 < Nat.card Eb := by
    have h1 : 16 ≤ 2 * Nat.card Eb := by
      calc 16 = r Q := hrQ16.symm
        _ = Nat.card E := hrE
        _ ≤ 2 * Nat.card Eb := hEcard
    norm_num
    omega
  obtain ⟨σ, hσE, hσout⟩ := A6.exists_not_inner_of_card_gt hBu.bender Eb hEbsq hEb8
  set Qb : Subgroup (MulAut (↥Lu ⧸ center ↥Lu)) := (Q.subgroupOf N).map (A6.barHom Lu) with hQb
  have hQbp : IsPGroup 2 Qb := by
    have h1 : IsPGroup 2 (Q.subgroupOf N) :=
      hQp.of_equiv (Subgroup.subgroupOfEquivOfLe (hQu.trans hCN)).symm
    exact h1.map _
  have hQbc : ∀ a ∈ Qb, ∀ b ∈ Qb, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hQc _ ha _ hb)
  have hσQ : σ ∈ Qb := by
    obtain ⟨w, hw, rfl⟩ := hσE
    exact ⟨w, hEQ hw, rfl⟩
  have hQb16 := A6.card_le_of_unitary_four hBu.bender Qb hQbp hQbc hσQ (hEbsq σ hσE) hσout
  have hQcard2 : Nat.card Q ≤ 2 * Nat.card Qb := by
    have h1 := A6.card_le_two_mul (A6.barHom Lu) (Q.subgroupOf N) (hker Q hQu)
    rwa [A6.card_subgroupOf (hQu.trans hCN)] at h1
  have : Nat.card Q ≤ 32 := by
    calc Nat.card Q ≤ 2 * Nat.card Qb := hQcard2
      _ ≤ 2 * 2 ^ 4 := Nat.mul_le_mul_left _ hQb16
      _ = 32 := by norm_num
  omega

theorem ZDSetup.prop131
    (S : ZDSetup X Z M) (h12 : Sec12Results Z M) : Prop131Stmt Z M := by
  intro c n i hL u hu hu2
  rcases h12.l1210 c n i hL with ⟨-, -, hall, -⟩ | ⟨-, -, hall, -⟩ | ⟨hi, -, hall, -⟩
  · exact (hall u hu hu2).1
  · exact (hall u hu hu2).1
  · exfalso
    subst hi
    exact A6.false_of_unitary S h12 hL (fun v hv hv2 => ⟨(hall v hv hv2).1, (hall v hv hv2).2.1⟩)
      hu hu2

end CFSG.GH74.Uniqueness
