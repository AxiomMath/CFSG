module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2012Fus2
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2012Model
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2012Hom
public import CFSG.GroupTheory.PrimeCorefreeQuasisimple

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2012

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Bg CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Final
  CFSG.GH74.GLS.Stage2.Final.Thm6 CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2
  CFSG.GH74.GLS.Stage2.Final.Thm6.SL2Bound CFSG.GH74.GLS.Stage2.Final.Thm6.L20

section T1

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {q : ℕ}
  {L₁ L₂ : Subgroup (CentralizerBar z)} {K₁ K₂ : Subgroup G}

theorem mem_normalizer_K₂_of_odd (hK : CompData z K₁ K₂ L₁ L₂) {c : G} (hcC : c ∈ Cen z)
    (hodd : Odd (orderOf c)) : c ∈ normalizer (K₂ : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hcinvC : c⁻¹ ∈ Cen z := (Cen z).inv_mem hcC
  have hcinvodd : Odd (orderOf c⁻¹) := by rwa [orderOf_inv]
  constructor
  · intro hx
    exact (hK.odd_norm c hcC hodd).2 x hx
  · intro hx
    have := (hK.odd_norm c⁻¹ hcinvC hcinvodd).2 _ hx
    simpa [mul_assoc] using this

theorem isCyclic_T₁
    (hP : Stage1Pair G z S q L₁ L₂) (hK : CompData z K₁ K₂ L₁ L₂) (hq9 : q ≠ 9)
    (hzI : z ∈ K₁ ⊓ K₂) (hz1 : z ≠ 1) {a₁ a₂ : G} (ha₁ : a₁ ∈ K₁) (ha₂ : a₂ ∈ K₂) (ha₁z : a₁ * a₁ = z) :
    IsCyclic ↥(K₁ ⊓ centralizer ({a₁ * a₂} : Set G)) := by
  have p₁ := pairK₁ hP hK hq9
  obtain ⟨F, iF, fF, e, hFq⟩ := sl2Equiv_of_model (hasSL2Model_comp₁ hP hK hq9)
  have hodd : Odd (Nat.card F) := hFq ▸ hP.odd
  set a' : ↥K₁ := ⟨a₁, ha₁⟩ with ha'
  have hcen2 : a' * a' ∈ center ↥K₁ := by
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    show (x : G) * (a₁ * a₁) = (a₁ * a₁) * x
    rw [ha₁z]
    exact hK.comm x x.2 z hzI.2
  have hncen : a' ∉ center ↥K₁ := by
    intro hc
    have hc' : ∀ c ∈ K₁, c * a₁ = a₁ * c := fun c hc'' => by
      have := Subgroup.mem_center_iff.1 hc ⟨c, hc''⟩
      exact congrArg Subtype.val this
    have : a₁ * a₁ = 1 := p₁.sq_of_mem_inf ⟨ha₁, p₁.cen ha₁ hc'⟩
    rw [ha₁z] at this
    exact hz1 this
  have hcyc := isCyclic_centralizer_sq e hodd hcen2 hncen
  have hmap : (centralizer ({a'} : Set ↥K₁)).map K₁.subtype = K₁ ⊓ centralizer ({a₁ * a₂} : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      have hy' : y ∈ centralizer ({a'} : Set ↥K₁) := hy
      rw [Subgroup.mem_centralizer_singleton_iff] at hy'
      show (y : G) ∈ centralizer ({a₁ * a₂} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : (y : G) * a₁ = a₁ * y := congrArg Subtype.val hy'
      have h2 : (y : G) * a₂ = a₂ * y := hK.comm y y.2 a₂ ha₂
      calc (y : G) * (a₁ * a₂) = (y * a₁) * a₂ := by group
        _ = (a₁ * y) * a₂ := by rw [h1]
        _ = a₁ * (y * a₂) := by group
        _ = a₁ * (a₂ * y) := by rw [h2]
        _ = (a₁ * a₂) * y := by group
    · rintro ⟨hxK, hxc⟩
      refine ⟨⟨x, hxK⟩, ?_, rfl⟩
      have hxc' : x ∈ centralizer ({a₁ * a₂} : Set G) := hxc
      rw [Subgroup.mem_centralizer_singleton_iff] at hxc'
      show (⟨x, hxK⟩ : ↥K₁) ∈ centralizer ({a'} : Set ↥K₁)
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      have h2 : x * a₂ = a₂ * x := hK.comm x hxK a₂ ha₂
      show x * a₁ = a₁ * x
      have h3 : x * (a₁ * a₂) = (a₁ * a₂) * x := hxc'
      have : (x * a₁) * a₂ = (a₁ * x) * a₂ := by
        calc (x * a₁) * a₂ = x * (a₁ * a₂) := by group
          _ = (a₁ * a₂) * x := h3
          _ = a₁ * (a₂ * x) := by group
          _ = a₁ * (x * a₂) := by rw [h2]
          _ = (a₁ * x) * a₂ := by group
      exact mul_right_cancel this
  have := (Subgroup.equivMapOfInjective (centralizer ({a'} : Set ↥K₁)) K₁.subtype K₁.subtype_injective).isCyclic.1 hcyc
  rw [hmap] at this
  exact this

omit [Finite G] in
theorem odd_mem_pPrimeCoreOf {T : Subgroup G} (hT : IsCyclic ↥T) {k : G} (hk : k ∈ T)
    (hodd : Odd (orderOf k)) : k ∈ pPrimeCoreOf 2 T := by
  have hcomm : ∀ x y : ↥T, x * y = y * x := fun x y => (IsCyclic.commGroup (α := ↥T)).mul_comm x y
  set N : Subgroup ↥T := Subgroup.zpowers (⟨k, hk⟩ : ↥T) with hN
  have hNn : N.Normal := ⟨fun n hn x => by
    have : x * n * x⁻¹ = n := by rw [hcomm x n]; group
    rw [this]
    exact hn⟩
  have hcop : Nat.Coprime 2 (Nat.card ↥N) := by
    rw [hN, Nat.card_zpowers, Subgroup.orderOf_mk]
    exact Nat.coprime_two_left.mpr hodd
  have := CFSG.GroupTheory.le_pPrimeCore_of_normal hNn hcop (Subgroup.mem_zpowers (⟨k, hk⟩ : ↥T))
  exact ⟨⟨k, hk⟩, this, rfl⟩

end T1

section Main

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {ε : Bool} {q : ℕ}
  {L₁ L₂ : Subgroup (CentralizerBar z)} {K₁ K₂ U : Subgroup G} {g : G}

theorem fused_conc201
    {k : Kind} {M : Subgroup G} (h11 : Lemma20_11) (hF : Fail20 G z k S M) (hMC : M = Cen z)
    (hT : TypeCl z k S) (hTL : TypeL4 z k S ε q) (hfused : Fused ε q)
    (h : FusedSetup z S ε q L₁ L₂ K₁ K₂ U g) : Conc201 z k S M := by
  classical
  have hP := h.L4.pair
  have hK := h.comp
  have p₁ := pairK₁ hP hK h.q9
  have hzI := z_mem_inf hP hK h.q9 (h.hUsup z h.zU)
  have hz1 := h.hz1
  have hz2 := h.hz2
  set t : G := g * z * g⁻¹ with ht
  have htU : t ∈ U := h.ht_mem
  have hUsq := four_sq h.U4
  have htt : t * t = 1 := hUsq t htU
  have ht1 : t ≠ 1 := by
    intro h1
    apply hz1
    have h2 : z = g⁻¹ * t * g := by rw [ht]; group
    rw [h2, h1]; group
  have htz : t ≠ z := h.gz
  obtain ⟨a₁, ha₁, a₂, ha₂, hta, ha₁z, ha₂z⟩ :=
    exists_ab hP hK h.q9 (h.hUsup z h.zU) hz1 (h.hUsup t htU) htt ht1 htz
  obtain ⟨e, heC, he₁, he₂, hec⟩ := swap_exists h
  have hecB : ∀ b ∈ Bsub z g, e * b = b * e := fun b hb => by
    obtain ⟨a, ha, rfl⟩ := mem_Bsub.1 hb
    exact hec a ha
  have hBK₁ := Bsub_inf_K₁ h he₁ hecB
  have hBcen := Bsub_cen_K₁ h11 hF hMC hT h he₂ hecB
  have hTcyc : IsCyclic ↥(K₁ ⊓ centralizer ({t} : Set G)) := by
    have := isCyclic_T₁ hP hK h.q9 hzI hz1 ha₁ ha₂ ha₁z
    rwa [← hta] at this
  set T₁ : Subgroup G := K₁ ⊓ centralizer ({t} : Set G) with hT₁
  set X₁ : Subgroup G := pPrimeCoreOf 2 T₁ with hX₁
  have hoddX : ∀ x ∈ T₁, Odd (orderOf x) → x ∈ X₁ := fun x hx ho => odd_mem_pPrimeCoreOf hTcyc hx ho
  have hX₁T : X₁ ≤ T₁ := Subgroup.map_subtype_le _
  have hX₁K : X₁ ≤ K₁ := fun x hx => (hX₁T hx).1
  have hX₁odd : ∀ x ∈ X₁, Odd (orderOf x) := fun x hx => odd_orderOf_of_mem_pPrimeCoreOf (F := T₁) hx
  have hX₁B : ∀ x ∈ X₁, ∀ b ∈ Bsub z g, x * b = b * x := by
    intro x hx b hb
    have hxT := hX₁T hx
    have hxK : x ∈ K₁ := hxT.1
    have hxt : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.1 hxT.2
    have h1 : x * b * x⁻¹ ∈ Bsub z g := conj_mem_Bsub hxt b hb
    have hbN : b ∈ normalizer (K₁ : Set G) := mem_normalizer_K₁_of_odd hK (Bsub_le_Cen h hb) (Bsub_odd b hb)
    have hc : x * b * x⁻¹ * b⁻¹ ∈ Bsub z g := (Bsub z g).mul_mem h1 ((Bsub z g).inv_mem hb)
    have hcK : x * b * x⁻¹ * b⁻¹ ∈ K₁ := by
      have h2 := (Subgroup.mem_normalizer_iff.1 hbN x⁻¹).1 (K₁.inv_mem hxK)
      have := K₁.mul_mem hxK h2
      simpa [mul_assoc] using this
    have h3 := hBK₁ _ hc hcK
    calc x * b = (x * b * x⁻¹ * b⁻¹) * b * x := by group
      _ = b * x := by rw [h3]; group
  have hZ : ∀ x ∈ X₁, (∀ y ∈ K₁, x * y = y * x) → x = 1 := by
    intro x hx hc
    have hxK : x ∈ K₁ := hX₁K hx
    have hxK₂ : x ∈ K₂ := p₁.cen hxK (fun c hc' => (hc c hc').symm)
    exact eq_one_of_sq_odd (p₁.sq_of_mem_inf ⟨hxK, hxK₂⟩) (hX₁odd x hx)
  have ha₁2 : a₁ * a₁ ≠ 1 := by rw [ha₁z]; exact hz1
  have hsq₁ : ∀ c ∈ K₁, c * (a₁ * a₁) = (a₁ * a₁) * c := fun c hc => by
    rw [ha₁z]; exact hK.comm c hc z hzI.2
  set Mset : Subgroup G := normalizer (K₁ : Set G) ⊓ normalizer (K₂ : Set G) ⊓ centralizer ({t} : Set G)
    with hMset
  have hMN : Mset ≤ normalizer (K₁ : Set G) := fun m hm => hm.1.1
  have hM : ∀ m ∈ Mset, ∀ c ∈ K₁, c * (m * a₁ * m⁻¹ * a₁⁻¹) = (m * a₁ * m⁻¹ * a₁⁻¹) * c := by
    intro m hm c hc
    have hmt : m * t = t * m := Subgroup.mem_centralizer_singleton_iff.1 hm.2
    have hζ : (m * a₂ * m⁻¹) * a₂⁻¹ ∈ K₂ :=
      K₂.mul_mem ((Subgroup.mem_normalizer_iff.1 hm.1.2 a₂).1 ha₂) (K₂.inv_mem ha₂)
    have hmt' : (m * a₁ * m⁻¹) * (m * a₂ * m⁻¹) = a₁ * a₂ := by
      calc (m * a₁ * m⁻¹) * (m * a₂ * m⁻¹) = m * (a₁ * a₂) * m⁻¹ := by group
        _ = m * t * m⁻¹ := by rw [hta]
        _ = t := by rw [hmt]; group
        _ = a₁ * a₂ := hta
    have hcomm1 : a₁⁻¹ * ((m * a₂ * m⁻¹) * a₂⁻¹) = ((m * a₂ * m⁻¹) * a₂⁻¹) * a₁⁻¹ :=
      hK.comm a₁⁻¹ (K₁.inv_mem ha₁) _ hζ
    have hwζ : (m * a₁ * m⁻¹ * a₁⁻¹) * ((m * a₂ * m⁻¹) * a₂⁻¹) = 1 := by
      calc (m * a₁ * m⁻¹ * a₁⁻¹) * ((m * a₂ * m⁻¹) * a₂⁻¹)
          = (m * a₁ * m⁻¹) * (a₁⁻¹ * ((m * a₂ * m⁻¹) * a₂⁻¹)) := by group
        _ = (m * a₁ * m⁻¹) * (((m * a₂ * m⁻¹) * a₂⁻¹) * a₁⁻¹) := by rw [hcomm1]
        _ = ((m * a₁ * m⁻¹) * (m * a₂ * m⁻¹)) * a₂⁻¹ * a₁⁻¹ := by group
        _ = 1 := by rw [hmt']; group
    have hw : (m * a₁ * m⁻¹ * a₁⁻¹) ∈ K₂ := by
      have := eq_inv_of_mul_eq_one_left hwζ
      rw [this]
      exact K₂.inv_mem hζ
    exact hK.comm c hc _ hw
  have hB : ∀ b ∈ Bsub z g, ∃ x ∈ X₁, ∀ y ∈ K₁, b * y * b⁻¹ = x * y * x⁻¹ := by
    intro b hb
    have hbC := Bsub_le_Cen h hb
    have hbodd := Bsub_odd b hb
    have hbN₁ := mem_normalizer_K₁_of_odd hK hbC hbodd
    have hbN₂ := mem_normalizer_K₂_of_odd hK hbC hbodd
    have hbt : b * t = t * b := Bsub_comm_U h b hb t htU
    have hbM : b ∈ Mset := ⟨⟨hbN₁, hbN₂⟩, Subgroup.mem_centralizer_singleton_iff.2 hbt⟩
    have hWodd : Odd (Nat.card ↥(Subgroup.zpowers b)) := by
      rw [Nat.card_zpowers]; exact hbodd
    have hWab : ∀ x ∈ Subgroup.zpowers b, ∀ y ∈ Subgroup.zpowers b, x * y = y * x := by
      intro x hx y hy
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      exact (Commute.zpow_zpow_self b m n).eq
    have hX : ∀ x ∈ K₁, Odd (orderOf x) → x * a₁ = a₁ * x →
        ∃ m ∈ Mset, (∀ y ∈ K₁, m * y * m⁻¹ = x * y * x⁻¹) ∧
          ∀ w ∈ Subgroup.zpowers b, m * w * m⁻¹ ∈ Subgroup.zpowers b := by
      intro x hx hxo hxa
      have hxa₂ : x * a₂ = a₂ * x := hK.comm x hx a₂ ha₂
      have hxt : x * t = t * x := by
        rw [hta]
        calc x * (a₁ * a₂) = (x * a₁) * a₂ := by group
          _ = (a₁ * x) * a₂ := by rw [hxa]
          _ = a₁ * (x * a₂) := by group
          _ = a₁ * (a₂ * x) := by rw [hxa₂]
          _ = (a₁ * a₂) * x := by group
      have hxT : x ∈ T₁ := ⟨hx, Subgroup.mem_centralizer_singleton_iff.2 hxt⟩
      have hxX := hoddX x hxT hxo
      have hxN := bar_sup_le_normalizer_inf hK.comm (Subgroup.mem_sup_left hx : x ∈ K₁ ⊔ K₂)
      refine ⟨x, ⟨⟨hxN.1, hxN.2⟩, Subgroup.mem_centralizer_singleton_iff.2 hxt⟩, fun y _ => rfl, ?_⟩
      intro w hw
      have hxb := hX₁B x hxX b hb
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
      have hc : Commute x b := hxb
      have : x * b ^ n * x⁻¹ = b ^ n := by
        rw [(hc.zpow_right n).eq]; group
      rw [this]
      exact Subgroup.mem_zpowers_iff.2 ⟨n, rfl⟩
    obtain ⟨x, hxK, hxo, hxa, hact⟩ := fit_G (K := K₁) (r := q) hP.odd hP.gt3
      (hasSL2Model_comp₁ hP hK h.q9) ha₁ ha₁2 hsq₁ Mset hMN hM (Subgroup.zpowers b)
      (Subgroup.zpowers_le.2 hbM) hWodd hWab hX b (Subgroup.mem_zpowers b)
    have hxa₂ : x * a₂ = a₂ * x := hK.comm x hxK a₂ ha₂
    have hxt : x * t = t * x := by
      rw [hta]
      calc x * (a₁ * a₂) = (x * a₁) * a₂ := by group
        _ = (a₁ * x) * a₂ := by rw [hxa]
        _ = a₁ * (x * a₂) := by group
        _ = a₁ * (a₂ * x) := by rw [hxa₂]
        _ = (a₁ * a₂) * x := by group
    exact ⟨x, hoddX x ⟨hxK, Subgroup.mem_centralizer_singleton_iff.2 hxt⟩ hxo, hact⟩
  obtain ⟨φ, hφ⟩ := exists_inj_hom hX₁K hZ hB hBcen
  have hXcyc : IsCyclic ↥X₁ :=
    (Subgroup.equivMapOfInjective (pPrimeCore 2 ↥T₁) T₁.subtype T₁.subtype_injective).isCyclic.1 inferInstance
  have hBcyc : IsCyclic ↥(Bsub z g) := isCyclic_of_injective φ hφ
  have hBdvd : Nat.card ↥(Bsub z g) ∣ Nat.card ↥X₁ := Subgroup.card_dvd_of_injective φ hφ
  have eqA : ↥(OddCore z) ≃* ↥(Bsub z g) :=
    Subgroup.equivMapOfInjective (OddCore z) (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  have hAcyc : IsCyclic ↥(OddCore z) := eqA.isCyclic.2 hBcyc
  have hAdvd : Nat.card ↥(OddCore z) ∣ Nat.card ↥X₁ := by
    rw [Nat.card_congr eqA.toEquiv]
    exact hBdvd
  have htN : t ∈ normalizer (K₁ : Set G) := (bar_sup_le_normalizer_inf hK.comm (h.hUsup t htU)).1
  subst hMC
  exact ⟨ε, q, hTL, rfl, K₁, K₂, compData_isCentralProd hP hK h.q9, hasSL2Model_comp₁ hP hK h.q9,
    hasSL2Model_comp₂ hP hK h.q9, hAcyc, t, isConj_iff.2 ⟨g, rfl⟩, h.US htU, htN, hAdvd,
    ⟨fun _ => hfused, fun _ => h.hUsup t htU⟩⟩

end Main

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2012
