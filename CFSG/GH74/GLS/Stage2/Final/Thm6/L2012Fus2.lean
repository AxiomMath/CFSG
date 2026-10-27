module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2012Swap
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2012Psp

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2012

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Bg CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Final
  CFSG.GH74.GLS.Stage2.Final.Thm6 CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2
  CFSG.GH74.GLS.Stage2.Final.Thm6.L20

section B

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {ε : Bool} {q : ℕ}
  {L₁ L₂ : Subgroup (CentralizerBar z)} {K₁ K₂ U : Subgroup G} {g : G}

@[expose] def Bsub (z g : G) : Subgroup G := (OddCore z).map (MulAut.conj g).toMonoidHom

omit [Finite G] in
theorem mem_Bsub {x : G} : x ∈ Bsub z g ↔ ∃ a ∈ OddCore z, g * a * g⁻¹ = x := by
  rw [Bsub, Subgroup.mem_map]
  rfl

theorem FusedSetup.hz2 (h : FusedSetup z S ε q L₁ L₂ K₁ K₂ U g) : z * z = 1 := by
  have h2 := h.ctx.orderOf_z
  have : z ^ 2 = 1 := by rw [← h2]; exact pow_orderOf_eq_one z
  simpa [pow_two] using this

theorem FusedSetup.hz1 (h : FusedSetup z S ε q L₁ L₂ K₁ K₂ U g) : z ≠ 1 := by
  have h2 := h.ctx.orderOf_z
  intro e
  rw [e, orderOf_one] at h2
  omega

theorem FusedSetup.hUsup (h : FusedSetup z S ε q L₁ L₂ K₁ K₂ U g) : ∀ u ∈ U, u ∈ K₁ ⊔ K₂ :=
  U_le_sup h.L4.pair h.comp h.ctx.S_le_Cen (h.L4.pair.base.four_le U h.US h.U4 h.Un) h.US h.U4

theorem FusedSetup.hAU (h : FusedSetup z S ε q L₁ L₂ K₁ K₂ U g) :
    ∀ a ∈ OddCore z, ∀ u ∈ U, a * u = u * a := fun a ha u hu =>
  h.comp.oddcomm a ha u (by rw [h.comp.layer]; exact h.hUsup u hu)

theorem FusedSetup.hgU (h : FusedSetup z S ε q L₁ L₂ K₁ K₂ U g) :
    ∀ u : G, u ∈ U ↔ g * u * g⁻¹ ∈ U := Subgroup.mem_normalizer_iff.1 h.gN

theorem FusedSetup.hgU' (h : FusedSetup z S ε q L₁ L₂ K₁ K₂ U g) : ∀ u ∈ U, g⁻¹ * u * g ∈ U := by
  intro u hu
  refine (h.hgU _).2 ?_
  have : g * (g⁻¹ * u * g) * g⁻¹ = u := by group
  rw [this]
  exact hu

theorem FusedSetup.ht_mem (h : FusedSetup z S ε q L₁ L₂ K₁ K₂ U g) : g * z * g⁻¹ ∈ U := (h.hgU z).1 h.zU

theorem FusedSetup.hcommU (h : FusedSetup z S ε q L₁ L₂ K₁ K₂ U g) :
    ∀ a ∈ OddCore z, ∀ u ∈ U, (g * a * g⁻¹) * u = u * (g * a * g⁻¹) := by
  intro a ha u hu
  have h1 := h.hAU a ha _ (h.hgU' u hu)
  calc g * a * g⁻¹ * u = g * (a * (g⁻¹ * u * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * u * g) * a) * g⁻¹ := by rw [h1]
    _ = u * (g * a * g⁻¹) := by group

theorem Bsub_comm_U (h : FusedSetup z S ε q L₁ L₂ K₁ K₂ U g) :
    ∀ b ∈ Bsub z g, ∀ u ∈ U, b * u = u * b := by
  intro b hb u hu
  obtain ⟨a, ha, rfl⟩ := mem_Bsub.1 hb
  exact h.hcommU a ha u hu

theorem Bsub_le_Cen (h : FusedSetup z S ε q L₁ L₂ K₁ K₂ U g) : Bsub z g ≤ Cen z := fun b hb => by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Bsub_comm_U h b hb z h.zU

theorem Bsub_odd : ∀ b ∈ Bsub z g, Odd (orderOf b) := by
  intro b hb
  obtain ⟨a, ha, rfl⟩ := mem_Bsub.1 hb
  have := MulEquiv.orderOf_eq (MulAut.conj g) a
  simp only [MulAut.conj_apply] at this
  rw [this]
  exact odd_orderOf_of_mem_pPrimeCoreOf (F := Cen z) ha

omit [Finite G] in
theorem conj_mem_Bsub {x : G} (hx : x * (g * z * g⁻¹) = (g * z * g⁻¹) * x) :
    ∀ b ∈ Bsub z g, x * b * x⁻¹ ∈ Bsub z g := by
  intro b hb
  obtain ⟨a, ha, rfl⟩ := mem_Bsub.1 hb
  have hy : g⁻¹ * x * g ∈ Cen z := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g⁻¹ * x * g * z = g⁻¹ * (x * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * x) * g := by rw [hx]
      _ = z * (g⁻¹ * x * g) := by group
  have hyN := Cen_le_normalizer_OddCore z hy
  have hya : g⁻¹ * x * g * a * (g⁻¹ * x * g)⁻¹ ∈ OddCore z := (Subgroup.mem_normalizer_iff.1 hyN a).1 ha
  refine mem_Bsub.2 ⟨_, hya, ?_⟩
  group

theorem F_inf_Bsub {k : Kind} {M : Subgroup G} (h11 : Lemma20_11) (hF : Fail20 G z k S M) (hMC : M = Cen z)
    (hT : TypeCl z k S) (h : FusedSetup z S ε q L₁ L₂ K₁ K₂ U g) :
    ∀ x ∈ F20 z, x ∈ Bsub z g → x = 1 := by
  have htS : zc z g⁻¹ ∈ S := by
    have : zc z g⁻¹ = g * z * g⁻¹ := by simp [zc]
    rw [this]
    exact h.US h.ht_mem
  have hnot : zc z g⁻¹ ∉ zpowers z := by
    intro hmem
    have : zc z g⁻¹ = g * z * g⁻¹ := by simp [zc]
    rw [this] at hmem
    rcases eq_one_or_eq_of_mem_zpowers h.hz2 hmem with h1 | h1
    · have h2 : z = g⁻¹ * (g * z * g⁻¹) * g := by group
      rw [h1] at h2
      apply h.hz1
      rw [h2]; group
    · exact h.gz h1
  have hbot := h11 G z k S M hF hMC hT g⁻¹ htS hnot
  intro x hxF hxB
  obtain ⟨a, ha, rfl⟩ := mem_Bsub.1 hxB
  have hxA : g * a * g⁻¹ ∈ Ag z g⁻¹ := by
    show g * a * g⁻¹ ∈ conjugate (OddCore z) g⁻¹
    rw [mem_conjugate_iff]
    simpa [mul_assoc] using ha
  have : g * a * g⁻¹ ∈ F20 z ⊓ Ag z g⁻¹ := ⟨hxF, hxA⟩
  rw [hbot] at this
  exact Subgroup.mem_bot.mp this

theorem F_comm_Bsub {k : Kind} {M : Subgroup G} (h11 : Lemma20_11) (hF : Fail20 G z k S M) (hMC : M = Cen z)
    (hT : TypeCl z k S) (h : FusedSetup z S ε q L₁ L₂ K₁ K₂ U g) :
    ∀ f ∈ F20 z, ∀ b ∈ Bsub z g, f * b = b * f := by
  intro f hf b hb
  have hfA : f ∈ OddCore z := F20_le_OddCore z hf
  have hft : f * (g * z * g⁻¹) = (g * z * g⁻¹) * f := h.hAU f hfA _ h.ht_mem
  have hbC : b ∈ Cen z := Bsub_le_Cen h hb
  have h1 : f * b * f⁻¹ ∈ Bsub z g := conj_mem_Bsub hft b hb
  have hc : f * b * f⁻¹ * b⁻¹ ∈ Bsub z g := (Bsub z g).mul_mem h1 ((Bsub z g).inv_mem hb)
  have hcF : f * b * f⁻¹ * b⁻¹ ∈ F20 z := by
    have := (F20 z).mul_mem hf (F20_conj_mem z hbC ((F20 z).inv_mem hf))
    simpa [mul_assoc] using this
  have := F_inf_Bsub h11 hF hMC hT h _ hcF hc
  calc f * b = (f * b * f⁻¹ * b⁻¹) * b * f := by group
    _ = b * f := by rw [this]; group

theorem oddCore_centralizer_le_F (z : G) {x : G} (hx : x ∈ OddCore z) (hc : ∀ f ∈ F20 z, f * x = x * f) :
    x ∈ F20 z := by
  have hodd : Odd (Nat.card ↥(OddCore z)) := by
    have h1 : Nat.card ↥(OddCore z) = Nat.card ↥(pPrimeCore 2 ↥(Cen z)) :=
      Nat.card_congr (Subgroup.equivMapOfInjective _ (Cen z).subtype (Cen z).subtype_injective).symm.toEquiv
    rw [h1]
    exact Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥(Cen z)))
  have hsolv : Group.IsSolvable ↥(OddCore z) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hx' : (⟨x, hx⟩ : ↥(OddCore z)) ∈ Subgroup.centralizer (fittingSubgroup ↥(OddCore z) : Set ↥(OddCore z)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyF : (y : G) ∈ F20 z := ⟨y, hy, rfl⟩
    exact Subtype.ext (hc _ hyF)
  have := centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv hx'
  exact ⟨⟨x, hx⟩, this, rfl⟩

theorem A_inf_Bsub {k : Kind} {M : Subgroup G} (h11 : Lemma20_11) (hF : Fail20 G z k S M) (hMC : M = Cen z)
    (hT : TypeCl z k S) (h : FusedSetup z S ε q L₁ L₂ K₁ K₂ U g) :
    ∀ x ∈ OddCore z, x ∈ Bsub z g → x = 1 := by
  intro x hxA hxB
  have hxF : x ∈ F20 z := oddCore_centralizer_le_F z hxA (fun f hf => F_comm_Bsub h11 hF hMC hT h f hf x hxB)
  exact F_inf_Bsub h11 hF hMC hT h x hxF hxB

theorem Bsub_inf_K₁
    (h : FusedSetup z S ε q L₁ L₂ K₁ K₂ U g) {e : G} (he₁ : ∀ a ∈ K₁, e * a * e⁻¹ ∈ K₂)
    (hec : ∀ b ∈ Bsub z g, e * b = b * e) : ∀ b ∈ Bsub z g, b ∈ K₁ → b = 1 := by
  intro b hb hb₁
  have hbe : e * b * e⁻¹ = b := by rw [hec b hb]; group
  have hb₂ : b ∈ K₂ := by
    have := he₁ b hb₁
    rwa [hbe] at this
  have p₁ := pairK₁ h.L4.pair h.comp h.q9
  have hzI := z_mem_inf h.L4.pair h.comp h.q9 (h.hUsup z h.zU)
  rcases p₁.inf_cases hzI h.hz1 ⟨hb₁, hb₂⟩ with h1 | h1
  · exact h1
  · exfalso
    have hodd := Bsub_odd b hb
    rw [h1, h.ctx.orderOf_z] at hodd
    exact absurd hodd (by decide)

theorem Bsub_cen_K₁
    {k : Kind} {M : Subgroup G} (h11 : Lemma20_11) (hF : Fail20 G z k S M) (hMC : M = Cen z)
    (hT : TypeCl z k S) (h : FusedSetup z S ε q L₁ L₂ K₁ K₂ U g) {e : G}
    (he₂ : ∀ b ∈ K₂, e * b * e⁻¹ ∈ K₁) (hec : ∀ b ∈ Bsub z g, e * b = b * e) :
    ∀ b ∈ Bsub z g, (∀ x ∈ K₁, b * x = x * b) → b = 1 := by
  intro b hb hbK₁
  have hbC := Bsub_le_Cen h hb
  have hbodd := Bsub_odd b hb
  have hb' : e⁻¹ * b * e = b := by
    calc e⁻¹ * b * e = e⁻¹ * (b * e) := by group
      _ = e⁻¹ * (e * b) := by rw [hec b hb]
      _ = b := by group
  have hbK₂ : ∀ y ∈ K₂, b * y = y * b := by
    intro y hy
    have h1 := hbK₁ _ (he₂ y hy)
    have hy'' : e⁻¹ * (e * y * e⁻¹) * e = y := by group
    calc b * y = (e⁻¹ * b * e) * (e⁻¹ * (e * y * e⁻¹) * e) := by rw [hb', hy'']
      _ = e⁻¹ * (b * (e * y * e⁻¹)) * e := by group
      _ = e⁻¹ * ((e * y * e⁻¹) * b) * e := by rw [h1]
      _ = (e⁻¹ * (e * y * e⁻¹) * e) * (e⁻¹ * b * e) := by group
      _ = y * b := by rw [hy'', hb']
  have hbA : b ∈ OddCore z := h.comp.odd_mem b hbC hbodd (fun a ha => hbK₁ a ha) hbK₂
  exact A_inf_Bsub h11 hF hMC hT h b hbA hb

end B

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2012
