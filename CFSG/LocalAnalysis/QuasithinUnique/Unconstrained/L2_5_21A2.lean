module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21A

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

section Orbit

variable {G : Type} [Group G] [Finite G]

theorem card_eq_four_mul_of_orbit {X E : Subgroup G} {t : G} (hE4 : Nat.card E = 4)
    (hO1 : ∀ n ∈ X, ∃ w ∈ E, n * t * n⁻¹ = t * w)
    (hO2 : ∀ w ∈ E, ∃ n ∈ X, n * t * n⁻¹ = t * w) :
    Nat.card X = 4 * Nat.card ↥(X ⊓ Subgroup.centralizer ({t} : Set G)) := by
  let : MulAction ↥X G :=
    MulAction.compHom G ((MulAut.conj : G →* MulAut G).comp X.subtype)
  have hsmul : ∀ (n : ↥X) (g : G), n • g = (n : G) * g * (n : G)⁻¹ := fun n g => rfl
  have hcard : Nat.card (MulAction.orbit ↥X t) * Nat.card (MulAction.stabilizer ↥X t) =
      Nat.card ↥X := by
    classical
    have : Fintype G := Fintype.ofFinite G
    have : Fintype ↥X := Fintype.ofFinite _
    have : Fintype (MulAction.orbit ↥X t) := Fintype.ofFinite _
    have : Fintype (MulAction.stabilizer ↥X t) := Fintype.ofFinite _
    simp only [Nat.card_eq_fintype_card]
    exact MulAction.card_orbit_mul_card_stabilizer_eq_card_group ↥X t
  have horb : Nat.card (MulAction.orbit ↥X t) = 4 := by
    rw [← hE4]
    symm
    refine Nat.card_congr (Equiv.ofBijective
      (fun w : E => (⟨t * (w : G), ?_⟩ : MulAction.orbit ↥X t)) ⟨?_, ?_⟩)
    · obtain ⟨n, hn, hnw⟩ := hO2 w w.2
      exact ⟨⟨n, hn⟩, by
        show (⟨n, hn⟩ : ↥X) • t = t * (w : G)
        rw [hsmul]; exact hnw⟩
    · intro w w' hww'
      have := congrArg Subtype.val hww'
      exact Subtype.ext (mul_left_cancel this)
    · rintro ⟨g, hg⟩
      obtain ⟨n, rfl⟩ := hg
      obtain ⟨w, hw, hnw⟩ := hO1 n n.2
      exact ⟨⟨w, hw⟩, Subtype.ext (by
        show t * w = n • t
        rw [hsmul]; exact hnw.symm)⟩
  have hstab : Nat.card (MulAction.stabilizer ↥X t) =
      Nat.card ↥(X ⊓ Subgroup.centralizer ({t} : Set G)) := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun n : MulAction.stabilizer ↥X t => (⟨((n : ↥X) : G), (n : ↥X).2, ?_⟩ :
        ↥(X ⊓ Subgroup.centralizer ({t} : Set G)))) ⟨?_, ?_⟩)
    · have h1 : (n : ↥X) • t = t := n.2
      rw [hsmul] at h1
      show (n : ↥X).1 ∈ Subgroup.centralizer ({t} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (n : ↥X).1 * t = ((n : ↥X).1 * t * (n : ↥X).1⁻¹) * (n : ↥X).1 := by group
        _ = t * (n : ↥X).1 := by rw [h1]
    · intro n n' h
      exact Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val h))
    · rintro ⟨y, hyX, hyC⟩
      refine ⟨⟨⟨y, hyX⟩, ?_⟩, rfl⟩
      show (⟨y, hyX⟩ : ↥X) • t = t
      rw [hsmul]
      have := Subgroup.mem_centralizer_singleton_iff.mp hyC
      calc y * t * y⁻¹ = t * y * y⁻¹ := by rw [this]
        _ = t := by group
  rw [horb, hstab] at hcard
  exact hcard.symm

end Orbit

section Klein4

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  {N : Notation25 hs}

theorem Facts258.four_normalizer_trans (h258 : Facts258 N) {E : Subgroup G} (hEK : E ≤ N.K)
    (hE4 : IsFourSubgroup E) {x y : G} (hx : x ∈ E) (hy : y ∈ E) (hx1 : x ≠ 1) (hy1 : y ≠ 1) :
    ∃ m ∈ N.K ⊓ Subgroup.normalizer (E : Set G), m⁻¹ * x * m = y := by
  let D : Klein.Data (N.K ⊓ Subgroup.normalizer (E : Set G)) E :=
    { φ := (h258.four_normalizer E hEK hE4).some
      le := fun _ he => ⟨hEK he, Subgroup.le_normalizer he⟩
      normal := inf_le_right
      card := hE4.2 }
  obtain ⟨a, b, ha, hb, ha1, hb1, hab, hgen, htr⟩ := D.exists_gens
  have hother : ∀ u ∈ E, u ≠ 1 → ∃ u₂ ∈ E, u₂ ≠ 1 ∧ u₂ ≠ u := by
    intro u hu hu1
    by_cases hua : u = a
    · exact ⟨b, hb, hb1, fun h' => hab (by rw [← hua, h'])⟩
    · exact ⟨a, ha, ha1, fun h' => hua h'.symm⟩
  obtain ⟨x₂, hx₂, hx₂1, hx₂x⟩ := hother x hx hx1
  obtain ⟨y₂, hy₂, hy₂1, hy₂y⟩ := hother y hy hy1
  obtain ⟨nx, hnx, hnxa, -⟩ := htr x hx x₂ hx₂ hx1 hx₂1 (Ne.symm hx₂x)
  obtain ⟨ny, hny, hnya, -⟩ := htr y hy y₂ hy₂ hy1 hy₂1 (Ne.symm hy₂y)
  refine ⟨nx⁻¹ * ny, (N.K ⊓ Subgroup.normalizer (E : Set G)).mul_mem
    ((N.K ⊓ Subgroup.normalizer (E : Set G)).inv_mem hnx) hny, ?_⟩
  have hxa : x = nx⁻¹ * a * nx := hnxa.symm
  have hya : y = ny⁻¹ * a * ny := hnya.symm
  calc (nx⁻¹ * ny)⁻¹ * x * (nx⁻¹ * ny) = ny⁻¹ * (nx * x * nx⁻¹) * ny := by group
    _ = ny⁻¹ * a * ny := by
      congr 2
      rw [hxa]; group
    _ = y := hya.symm

end Klein4

section Normalizer

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_forall_mem {F : Subgroup G} {n : G} (h : ∀ f ∈ F, n * f * n⁻¹ ∈ F) :
    n ∈ Subgroup.normalizer (F : Set G) := by
  have hle : F ≤ CFSG.conjugate F n := fun f hf => (BenderBranch.mem_conjugate_iff).mpr (h f hf)
  have heq : F = CFSG.conjugate F n :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [BenderBranch.card_conjugate])
  exact BenderBranch.conjugate_eq_iff_mem_normalizer.mp heq.symm

end Normalizer

section OrbitA2

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  {N : Notation25 hs} {t zK : G}

theorem Lv2520.caseA2_orbit_le {R : Subgroup ↥(autOn N.S N.K)} (h : Lv2520 N t zK)
    (hp : CaseAParams N t zK R) (hone : OutOneClass) (hfam : OutFamily N.K N.H)
    {E : Subgroup G} (hd : CaseAData N zK E) :
    ∀ n ∈ Subgroup.normalizer ((E ⊔ N.SC : Subgroup G) : Set G),
      ∃ w ∈ E, n * t * n⁻¹ = t * w := by
  intro n hn
  have hf := h.facts2511
  have hEK : E ≤ N.K := hd.le_SK.trans N.SK_le_K
  have hcommES : ∀ e ∈ E, ∀ a ∈ N.SC, e * a = a * e := fun e he a ha =>
    (h.SC_commutes ha e (hEK he)).symm
  have htF : t ∈ E ⊔ N.SC := Subgroup.mem_sup_right hf.t_mem
  have h1 : n * t * n⁻¹ ∈ E ⊔ N.SC := (Subgroup.mem_normalizer_iff.mp hn t).mp htF
  obtain ⟨w, hw, a, ha, hwa⟩ := mem_sup_of_commute hcommES h1
  rcases mem_zpowers_involution hf.t_mul_t (hp.SC_eq ▸ ha) with h2 | h2
  · exfalso
    rw [h2, mul_one] at hwa
    have hw2 : w * w = 1 := hd.four.sq hw
    have hw1 : w ≠ 1 := by
      intro hw1
      apply hf.t_ne_one
      calc t = n⁻¹ * (n * t * n⁻¹) * n := by group
        _ = 1 := by rw [← hwa, hw1]; group
    obtain ⟨c, hc⟩ := h.involution_conj_z hp hone hfam (hEK hw) hw2 hw1
    have h3 : (c * n)⁻¹ * N.z * (c * n) = t := by
      calc (c * n)⁻¹ * N.z * (c * n) = n⁻¹ * (c⁻¹ * N.z * c) * n := by group
        _ = n⁻¹ * (n * t * n⁻¹) * n := by rw [hc, hwa]
        _ = t := by group
    exact hf.not_conj (c * n) h3
  · refine ⟨w, hw, ?_⟩
    rw [h2] at hwa
    rw [← hwa]
    exact (h.SC_commutes hf.t_mem w (hEK hw)).symm

theorem Lv2520.K_le_normalizer_SC (h : Lv2520 N t zK) :
    N.K ≤ Subgroup.normalizer (N.SC : Set G) := by
  have hc : ∀ k ∈ N.K, ∀ a ∈ N.SC, k * a * k⁻¹ = a := by
    intro k hk a ha
    have := h.SC_commutes ha k hk
    calc k * a * k⁻¹ = a * k * k⁻¹ := by rw [← this]
      _ = a := by group
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [hc k hk x hx]
    exact hx
  · intro hx
    have h2 := hc k⁻¹ (N.K.inv_mem hk) _ hx
    have h3 : k⁻¹ * (k * x * k⁻¹) * k⁻¹⁻¹ = x := by group
    rw [h3] at h2
    rw [h2]
    exact hx

theorem Lv2520.caseA2_orbit_ge {R : Subgroup ↥(autOn N.S N.K)} (h : Lv2520 N t zK)
    (hp : CaseAParams N t zK R) (hone : OutOneClass) (hfam : OutFamily N.K N.H)
    (hin : N.S ≤ N.K ⊔ N.SC) {E : Subgroup G} (hd : CaseAData N zK E) :
    ∀ w ∈ E, ∃ n ∈ Subgroup.normalizer ((E ⊔ N.SC : Subgroup G) : Set G),
      n * t * n⁻¹ = t * w := by
  intro w hw
  by_cases hw1 : w = 1
  · exact ⟨1, (Subgroup.normalizer _).one_mem, by rw [hw1]; group⟩
  have hf := h.facts2511
  have h258 := h.facts258
  have hEK : E ≤ N.K := hd.le_SK.trans N.SK_le_K
  have hzKK : zK ∈ N.K := h.hK0 ▸ hf.zK_mem
  have hcommES : ∀ e ∈ E, ∀ a ∈ N.SC, e * a = a * e := fun e he a ha =>
    (h.SC_commutes ha e (hEK he)).symm
  have htSC : t ∈ N.SC := hf.t_mem
  have ht2 := hf.t_mul_t
  have hzK2 := hf.zK_sq
  obtain ⟨e, heE, he1, hezK⟩ : ∃ e ∈ E, e ≠ 1 ∧ e ≠ zK := by
    by_contra hno
    push Not at hno
    have hle : E ≤ Subgroup.zpowers zK := fun e he => by
      by_cases he1 : e = 1
      · rw [he1]; exact Subgroup.one_mem _
      · rw [hno e he he1]; exact Subgroup.mem_zpowers _
    have h1 := Subgroup.card_le_of_le hle
    have h2 : Nat.card (Subgroup.zpowers zK) = 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (by rw [pow_two]; exact hzK2) h.zK_ne_one
    have h3 := hd.four.2
    omega
  have he2 : e * e = 1 := hd.four.sq heE
  obtain ⟨g, hg⟩ := h.tw_conj hp hone hfam hd e heE
  have hEg := h.caseA2_E_le_conj hp hone hfam hin hd heE hg
  have hmemE' : ∀ y : G, y ∈ CFSG.conjugate E g⁻¹ ↔ g⁻¹ * y * g ∈ E := by
    intro y
    rw [BenderBranch.mem_conjugate_iff]
    simp
  have hE'K : CFSG.conjugate E g⁻¹ ≤ N.K := by
    intro y hy
    have h1 := hEg ((hmemE' y).mp hy)
    rw [BenderBranch.mem_conjugate_iff] at h1
    have e1 : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
    rwa [e1] at h1
  have hE'4 : IsFourSubgroup (CFSG.conjugate E g⁻¹) :=
    ⟨isElemAbelian_conjugate hd.four.1 g⁻¹, by rw [BenderBranch.card_conjugate]; exact hd.four.2⟩
  have hx₀ : g * e * g⁻¹ ∈ CFSG.conjugate E g⁻¹ := by
    rw [hmemE']
    have e1 : g⁻¹ * (g * e * g⁻¹) * g = e := by group
    rw [e1]; exact heE
  have hy₀ : g * zK * g⁻¹ ∈ CFSG.conjugate E g⁻¹ := by
    rw [hmemE']
    have e1 : g⁻¹ * (g * zK * g⁻¹) * g = zK := by group
    rw [e1]; exact hd.zK_mem
  have hx₀1 : g * e * g⁻¹ ≠ 1 := by
    intro h1
    apply he1
    calc e = g⁻¹ * (g * e * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  have hy₀1 : g * zK * g⁻¹ ≠ 1 := by
    intro h1
    apply h.zK_ne_one
    calc zK = g⁻¹ * (g * zK * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  obtain ⟨m, hmN, hm⟩ := h258.four_normalizer_trans hE'K hE'4 hx₀ hy₀ hx₀1 hy₀1
  have hmK : m ∈ N.K := hmN.1
  have hmt : m⁻¹ * t * m = t := by
    have := h.SC_commutes htSC m hmK
    calc m⁻¹ * t * m = m⁻¹ * (t * m) := by group
      _ = m⁻¹ * (m * t) := by rw [this]
      _ = t := by group
  obtain ⟨n₂, hn₂⟩ : ∃ n₂ : G, n₂ = g⁻¹ * m⁻¹ * g := ⟨_, rfl⟩
  have hn₂e : n₂ * e * n₂⁻¹ = zK := by
    rw [hn₂]
    calc g⁻¹ * m⁻¹ * g * e * (g⁻¹ * m⁻¹ * g)⁻¹ = g⁻¹ * (m⁻¹ * (g * e * g⁻¹) * m) * g := by group
      _ = g⁻¹ * (g * zK * g⁻¹) * g := by rw [hm]
      _ = zK := by group
  have hn₂t' : n₂ * (t * e) * n₂⁻¹ = t * e := by
    rw [hn₂, ← hg]
    calc g⁻¹ * m⁻¹ * g * (g⁻¹ * t * g) * (g⁻¹ * m⁻¹ * g)⁻¹ = g⁻¹ * (m⁻¹ * t * m) * g := by group
      _ = g⁻¹ * t * g := by rw [hmt]
  have hn₂t : n₂ * t * n₂⁻¹ = t * (e * zK) := by
    calc n₂ * t * n₂⁻¹ = (n₂ * (t * e) * n₂⁻¹) * (n₂ * e * n₂⁻¹) := by
          have : t = (t * e) * e := by
            calc t = t * (e * e) := by rw [he2]; group
              _ = (t * e) * e := by group
          conv_lhs => rw [this]
          group
      _ = (t * e) * zK := by rw [hn₂t', hn₂e]
      _ = t * (e * zK) := by group
  have hn₂E : ∀ e'' ∈ E, n₂ * e'' * n₂⁻¹ ∈ E := by
    intro e'' he''
    have h1 : g * e'' * g⁻¹ ∈ CFSG.conjugate E g⁻¹ := by
      rw [hmemE']
      have e1 : g⁻¹ * (g * e'' * g⁻¹) * g = e'' := by group
      rw [e1]; exact he''
    have h2 := (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer ((CFSG.conjugate E g⁻¹ : Subgroup G) : Set G)).inv_mem hmN.2) _).mp h1
    rw [hmemE'] at h2
    have e1 : g⁻¹ * (m⁻¹ * (g * e'' * g⁻¹) * m⁻¹⁻¹) * g = n₂ * e'' * n₂⁻¹ := by
      rw [hn₂]; group
    rwa [e1] at h2
  set w₁ : G := e * zK with hw₁
  have hw₁E : w₁ ∈ E := E.mul_mem heE hd.zK_mem
  have hw₁1 : w₁ ≠ 1 := by
    intro h1
    apply hezK
    calc e = (e * zK) * zK := by calc e = e * (zK * zK) := by rw [hzK2]; group
                                     _ = (e * zK) * zK := by group
      _ = zK := by rw [← hw₁, h1, one_mul]
  have hFmem : ∀ f ∈ E ⊔ N.SC, ∃ e'' ∈ E, ∃ a ∈ N.SC, e'' * a = f := fun f hf' =>
    mem_sup_of_commute hcommES hf'
  have hn₂F : n₂ ∈ Subgroup.normalizer ((E ⊔ N.SC : Subgroup G) : Set G) := by
    refine mem_normalizer_of_forall_mem fun f hf' => ?_
    obtain ⟨e'', he'', a, ha, rfl⟩ := hFmem f hf'
    have e1 : n₂ * (e'' * a) * n₂⁻¹ = (n₂ * e'' * n₂⁻¹) * (n₂ * a * n₂⁻¹) := by group
    rw [e1]
    refine (E ⊔ N.SC).mul_mem (Subgroup.mem_sup_left (hn₂E e'' he'')) ?_
    rcases mem_zpowers_involution ht2 (hp.SC_eq ▸ ha) with h1 | h1
    · rw [h1]; simp
    · rw [h1, hn₂t]
      exact (E ⊔ N.SC).mul_mem (Subgroup.mem_sup_right htSC) (Subgroup.mem_sup_left
        (E.mul_mem heE hd.zK_mem))
  obtain ⟨m₁, hm₁N, hm₁⟩ := h258.four_normalizer_trans hEK hd.four hw₁E hw hw₁1 hw1
  have hm₁K : m₁ ∈ N.K := hm₁N.1
  have hn₁F : m₁⁻¹ ∈ Subgroup.normalizer ((E ⊔ N.SC : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_sup E N.SC
      ⟨(Subgroup.normalizer (E : Set G)).inv_mem hm₁N.2,
        (Subgroup.normalizer (N.SC : Set G)).inv_mem (h.K_le_normalizer_SC hm₁K)⟩
  have hn₁t : m₁⁻¹ * t * m₁ = t := by
    have := h.SC_commutes htSC m₁ hm₁K
    calc m₁⁻¹ * t * m₁ = m₁⁻¹ * (t * m₁) := by group
      _ = m₁⁻¹ * (m₁ * t) := by rw [this]
      _ = t := by group
  refine ⟨m₁⁻¹ * n₂, (Subgroup.normalizer _).mul_mem hn₁F hn₂F, ?_⟩
  calc m₁⁻¹ * n₂ * t * (m₁⁻¹ * n₂)⁻¹ = m₁⁻¹ * (n₂ * t * n₂⁻¹) * m₁ := by group
    _ = m₁⁻¹ * (t * w₁) * m₁ := by rw [hn₂t]
    _ = (m₁⁻¹ * t * m₁) * (m₁⁻¹ * w₁ * m₁) := by group
    _ = t * w := by rw [hn₁t, hm₁]

theorem Lv2520.caseA2_false {R : Subgroup ↥(autOn N.S N.K)} (h : Lv2520 N t zK)
    (hp : CaseAParams N t zK R) (hone : OutOneClass) (hfam : OutFamily N.K N.H)
    (hin : N.S ≤ N.K ⊔ N.SC) : False := by
  have hf := h.facts2511
  obtain ⟨E, hd⟩ := h.exists_caseAData hp.ds hp.hz
  set X : Subgroup G := Subgroup.normalizer ((E ⊔ N.SC : Subgroup G) : Set G) with hX
  have hcard := card_eq_four_mul_of_orbit (X := X) (E := E) (t := t) hd.four.2
    (h.caseA2_orbit_le hp hone hfam hd) (h.caseA2_orbit_ge hp hone hfam hin hd)
  set Y : Subgroup G := X ⊓ Subgroup.centralizer ({t} : Set G) with hY
  have hU := hd.sylow
  have hUX : N.S ⊓ Subgroup.normalizer (E : Set G) ≤ X := hU.1
  have hSt : N.S ≤ Subgroup.centralizer ({t} : Set G) := by
    intro s hs'
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hf.t_mem_center.2 s hs'
  have hUY : N.S ⊓ Subgroup.normalizer (E : Set G) ≤ Y :=
    le_inf hUX (inf_le_left.trans hSt)
  have hYX : Y ≤ X := inf_le_left
  have h1 : (N.S ⊓ Subgroup.normalizer (E : Set G)).relIndex Y * Y.relIndex X =
      (N.S ⊓ Subgroup.normalizer (E : Set G)).relIndex X :=
    Subgroup.relIndex_mul_relIndex _ _ _ hUY hYX
  have hYX4 : Y.relIndex X = 4 := by
    have h2 := Subgroup.card_mul_index (Y.subgroupOf X)
    have h3 : Nat.card (Y.subgroupOf X) = Nat.card Y :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYX).toEquiv
    rw [h3] at h2
    have hpos : 0 < Nat.card Y := Nat.card_pos
    have h4 : Nat.card Y * (Y.subgroupOf X).index = Nat.card Y * 4 := by
      rw [h2, hcard]; ring
    exact Nat.eq_of_mul_eq_mul_left hpos h4
  apply hU.2.2
  have h5 : (N.S ⊓ Subgroup.normalizer (E : Set G)).relIndex X =
      (N.S ⊓ Subgroup.normalizer (E : Set G)).relIndex Y * 4 := by rw [← h1, hYX4]
  show 2 ∣ (N.S ⊓ Subgroup.normalizer (E : Set G)).relIndex X
  rw [h5]
  exact Dvd.dvd.mul_left (by norm_num) _

theorem Lv2520.caseA_false {R : Subgroup ↥(autOn N.S N.K)} (h : Lv2520 N t zK)
    (hR : DS.DSData R) (hidx : Nat.card ↥N.S ≤ 2 * (Nat.card ↥N.SK * Nat.card ↥N.SC))
    (hA2 : Nat.card ↥N.SC = 2) (hone : OutOneClass) (houter : OutOuter)
    (hfam : OutFamily N.K N.H) : False := by
  have hp := h.caseAParams hR hidx hA2
  by_cases hin : N.S ≤ N.K ⊔ N.SC
  · exact h.caseA2_false hp hone hfam hin
  · exact h.caseA1_false hp hone houter hfam hin

end OrbitA2

end CFSG.QuasithinUnique
