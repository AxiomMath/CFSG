module

public import CFSG.Certificates.Kernel.J2EnumSound
public import CFSG.Certificates.Kernel.J2Enum.Group
public import CFSG.Certificates.Kernel.Child3Reps
import all CFSG.Certificates.Kernel.J2Enum.Classes
import CFSG.Certificates.Kernel.J2CoverSnd.Chain
import CFSG.Certificates.Kernel.KGC31PSound

public section

namespace CFSG.KC.J2Enum.CntPf

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Child3 CFSG.Monster.B.Co2.Native
open CFSG.Certificates.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.ComponentClassification.J2Cover CFSG.KC.J2Enum
open CFSG.Sporadic.Th (Rep idx_of_lt Rep.compT Rep.idT)
open CFSG.Sporadic.SmallOddCore (conjClass self_mem_conjClass)

theorem exists_of_forall₂' {α β : Type*} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ a ∈ l₁, ∃ b ∈ l₂, R a b
  | _, _, .nil, _, h => absurd h List.not_mem_nil
  | _, _, .cons hr hs, a, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨_, List.mem_cons_self, hr⟩
    · obtain ⟨b, hb, hab⟩ := exists_of_forall₂' hs a h
      exact ⟨b, List.mem_cons_of_mem _ hb, hab⟩

theorem mem_records' {n w kS kO BP NS CH g N cap mx : ℕ} {PS PSI LR TR TRI : ℕ → ℕ}
    {D : List (List ℤ)} {S : Array (Array ℕ)} {base : Array ℕ}
    {GP GIP CI E P L K Ss SI : ℕ → ℕ} {CS OFF : List ℕ}
    (hb : Binds n w PS kS 3 BP S base)
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D 3 BP = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS 3 BP) (hNS : n ≤ NS * CH)
    (hs : ∀ i < 3, ∀ s < NS, schK n w (mask w) (n * w) (pidn n w) PS PSI LR TR TRI kS BP 3 i
      (stepsAt n w PS kS BP i) (s * CH) CH = true)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true) (hgk : g ≤ kO)
    (hgp : ∀ l < g, GP l = PS l ∧ GIP l = PSI l) (hkO : kO ≤ g)
    (hoff : offOK CS OFF N = true)
    (h : ∀ j < N, repK n w GP GIP g CS OFF CI E P L K Ss SI N cap j = true)
    (hrep : ∀ i < CS.length, canonK n w (mask w) (n * w) (E (lget OFF i)) = true ∧
      siftK n w (mask w) (n * w) (pidn n w) LR TRI BP 3 0 (E (lget OFF i)) = true ∧
      ordTest n mx (arrTable n (unpack n w (E (lget OFF i)))) = true)
    (hN : (filterProducts n (ordTest n mx) (chainTables n S base) (idT n) []).length = N) :
    ∀ T ∈ filterProducts n (ordTest n mx) (chainTables n S base) (idT n) [],
      ∃ j < N, T = tabP n w (E j) := by
  classical
  have hgO : g = kO := le_antisymm hgk hkO
  subst hgO
  obtain ⟨-, -, hsift, -⟩ := GrpPf.group3 hb hh hl hNS hs
  obtain ⟨hT, hsurj, hinj⟩ := GrpPf.enum3 hb hh hl hNS hs
  have hn : n < 16777216 := by have := hb.2.2.1; omega
  have hn32 : n < 2 ^ 32 := by omega
  have hkS : g ≤ kS := hb.2.2.2.1 ▸ (Raw.Orb.rawHeadOK_of hb hh).1
  obtain ⟨G, hG⟩ : ∃ G, G = Raw.Orb.Gen n S g := ⟨_, rfl⟩
  rw [← hG] at hT hsurj hsift
  obtain ⟨gg, hggd⟩ : ∃ gg : ℕ → Equiv.Perm (Fin n),
      gg = fun l => CFSG.Monster.B.Co2.permOfArr n S[l]! := ⟨_, rfl⟩
  have hgg : ∀ l < g, Raw.Orb.PRep n w (GP l) (gg l) ∧ Raw.Orb.PRep n w (GIP l) (gg l)⁻¹ ∧
      gg l ∈ G := by
    intro l hl
    obtain ⟨e1, e2⟩ := hgp l hl
    obtain ⟨p1, p2⟩ := Raw.Orb.prep_PS hb hp (j := l) (by omega)
    rw [e1, e2, hggd, hG]
    exact ⟨p1, p2, Subgroup.subset_closure ⟨⟨l, hl⟩, rfl⟩⟩
  set τ : ℕ → ℕ → Equiv.Perm (Fin n) := fun j k => CFSG.Certificates.ChainArrays.levT n S base j k
    with hτ
  obtain ⟨P3, hP3⟩ : ∃ P3 : List (Equiv.Perm (Fin n)),
      P3 = trip (rcnt (LR 0)) (rcnt (LR 1)) (rcnt (LR 2)) fun a b c => τ 0 a * τ 1 b * τ 2 c :=
    ⟨_, rfl⟩
  have hP3nd : P3.Nodup := by
    rw [hP3]
    exact trip_nodup hinj
  have hP3mem : ∀ x, x ∈ P3 ↔ x ∈ G := by
    intro x
    rw [hP3, mem_trip]
    constructor
    · rintro ⟨a, ha, b, hb', c, hc, rfl⟩
      exact mul_mem (mul_mem (hT 0 (by norm_num) a ha).1 (hT 1 (by norm_num) b hb').1)
        (hT 2 (by norm_num) c hc).1
    · exact hsurj x
  obtain ⟨hct, -⟩ := CFSG.KC.J2Cover.Snd.chainTables_eq_lvTab hb hp hl
  have hA : List.Forall₂ (Rep n) (allProd n (chainTables n S base) (idT n)) P3 := by
    rw [hct, allProd3, hP3]
    refine forall₂_trip fun a ha b hb' c hc => ?_
    have := ((Rep.idT hn32).compT (rep_of_prep hn32 (hT 0 (by norm_num) a ha).2)).compT
      (rep_of_prep hn32 (hT 1 (by norm_num) b hb').2) |>.compT
      (rep_of_prep hn32 (hT 2 (by norm_num) c hc).2)
    rwa [one_mul] at this
  have hX : List.Forall₂ (Rep n) (filterProducts n (ordTest n mx) (chainTables n S base)
      (idT n) []) (P3.filter fun x => ordS x mx).reverse := by
    rw [filterProducts_eq, List.append_nil, List.forall₂_reverse_iff]
    exact List.rel_filter
      (fun T x hTx => show ordTest n mx T = true ↔ ordS x mx = true by rw [ordTest_eq hTx]) hA
  have hXmem : ∀ x, x ∈ (P3.filter fun x => ordS x mx).reverse ↔ x ∈ G ∧ ordS x mx = true := by
    intro x
    rw [List.mem_reverse, List.mem_filter, hP3mem]
  set xs := (P3.filter fun x => ordS x mx).reverse with hxs
  obtain ⟨hoffv, hsum⟩ := offOK_facts hoff
  have F := fun j (hj : j < N) => repK_facts (h j hj)
  obtain ⟨ε, hεd⟩ : ∃ ε : ℕ → Equiv.Perm (Fin n),
      ε = fun j => Classical.epsilon (Raw.Orb.PRep n w (E j)) := ⟨_, rfl⟩
  have hε : ∀ j γ, Raw.Orb.PRep n w (E j) γ → ε j = γ := fun j γ hγ => by
    rw [hεd]
    exact prep_unique (Classical.epsilon_spec (p := Raw.Orb.PRep n w (E j)) ⟨γ, hγ⟩) hγ
  have hρ : ∀ i < CS.length, Raw.Orb.PRep n w (E (lget OFF i)) (ε (lget OFF i)) ∧
      ε (lget OFF i) ∈ G ∧ ordS (ε (lget OFF i)) mx = true := by
    intro i hi
    obtain ⟨hc, hsf, ho⟩ := hrep i hi
    obtain ⟨γ, hγG, hγ⟩ := (hsift _ hc).1 hsf
    rw [hε _ _ hγ]
    exact ⟨hγ, hγG, by rw [← ordTest_eq (rep_of_prep hn32 hγ)]; exact ho⟩
  have hcls : ∀ i < CS.length, ∀ k < lget CS i, Raw.Orb.PRep n w (E (lget OFF i + k))
      (ε (lget OFF i + k)) ∧ ε (lget OFF i + k) ∈
        conjClass G (ε (lget OFF i)) := by
    intro i hi k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · rw [Nat.add_zero]
        exact ⟨(hρ i hi).1, self_mem_conjClass _ _⟩
      · obtain ⟨hjN, hci⟩ := ci_eq hoff h hi hk
        have hkj : lget OFF i + k - lget OFF (CI (lget OFF i + k)) = k := by rw [hci]; omega
        obtain ⟨hP, hL, hcj⟩ := (F _ hjN).tree (by rw [hkj]; omega)
        rw [hkj] at hP
        rw [hci] at hcj
        obtain ⟨r1, r2⟩ := ih _ hP (by omega)
        obtain ⟨g1, g2, g3⟩ := hgg _ hL
        have hr : Raw.Orb.PRep n w (E (lget OFF i + k))
            (gg (L (lget OFF i + k)) * ε (lget OFF i + P (lget OFF i + k)) *
              (gg (L (lget OFF i + k)))⁻¹) := by
          rw [← hcj]
          exact Raw.Orb.prep_pcomp hn32 (Raw.Orb.prep_pcomp hn32 g1 r1) g2
        rw [hε _ _ hr]
        exact ⟨hr, CFSG.KS.SporSch.ClsSpec.conj_mem_conjClass g3 r2⟩
  have hεN : ∀ j < N, CI j < CS.length ∧ lget OFF (CI j) + (j - lget OFF (CI j)) = j ∧
      j - lget OFF (CI j) < lget CS (CI j) := fun j hj =>
    ⟨(F j hj).ci_lt, by have := (F j hj).off_le; omega, (F j hj).loc_lt⟩
  have hεG : ∀ j < N, Raw.Orb.PRep n w (E j) (ε j) ∧
      ε j ∈ conjClass G (ε (lget OFF (CI j))) := by
    intro j hj
    obtain ⟨h1, h2, h3⟩ := hεN j hj
    have := hcls _ h1 _ h3
    rwa [h2] at this
  have hεinj : ∀ a < N, ∀ b < N, ε a = ε b → a = b := by
    intro a ha b hb e
    apply E_inj h ha hb
    obtain ⟨-, -, hA0, -⟩ := PF.canon_facts (F a ha).canon
    obtain ⟨-, hw, hB0, -⟩ := PF.canon_facts (F b hb).canon
    refine PF.eq_of_fields (PF.w_pos hw) hA0 hB0 fun i hi => ?_
    rw [(hεG a ha).1 ⟨i, hi⟩, (hεG b hb).1 ⟨i, hi⟩, e]
  have hεxs : ∀ j < N, ε j ∈ xs := by
    intro j hj
    obtain ⟨c, hc, e⟩ := (hεG j hj).2
    obtain ⟨-, h2, h3⟩ := hρ _ (hεN j hj).1
    rw [hxs, hXmem, e, ordS_conj]
    exact ⟨mul_mem (mul_mem hc h2) (inv_mem hc), h3⟩
  set εs := (List.range N).map ε with hεs
  have hεsnd : εs.Nodup := List.Nodup.map_on (fun a ha b hb e =>
    hεinj a (List.mem_range.1 ha) b (List.mem_range.1 hb) e) List.nodup_range
  have hxslen : xs.length = N := by rw [← hX.length_eq, hN]
  have hperm : εs.Perm xs := by
    refine (hεsnd.subperm fun y hy => ?_).perm_of_length_le (by rw [hxslen, hεs]; simp)
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
    exact hεxs j (List.mem_range.1 hj)
  intro T hTm
  obtain ⟨x, hx, hTx⟩ := exists_of_forall₂' hX T hTm
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 (hperm.symm.subset hx)
  have hj' := List.mem_range.1 hj
  refine ⟨j, hj', ?_⟩
  have hsz : T.size = n :=
    CFSG.KC.KGC31P.filterProducts_size _ (idT n) [] (by simp [idT])
      (fun _ h => absurd h List.not_mem_nil) T hTm
  exact CFSG.KC.KGC31P.eq_tabP_of_rep hn32 hsz hTx
    (CFSG.KC.KGC31P.imageList_of_prep (hεG j hj').1)

end CFSG.KC.J2Enum.CntPf

namespace CFSG.KC.J2Enum

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Child3 CFSG.Monster.B.Co2.Native
open CFSG.Certificates.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.ComponentClassification.J2Cover

theorem mem_records {n w kS kO BP NS CH g N cap mx : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {D : List (List Int)} {S : Array (Array Nat)} {base : Array Nat}
    {GP GIP CI E P L K Ss SI : Nat → Nat} {CS OFF : List Nat}
    (hc : ChainOK3 n w kS kO BP NS CH PS PSI LR TR TRI D S base) (hgk : g ≤ kO)
    (hgp : ∀ l < g, GP l = PS l ∧ GIP l = PSI l) (hkO : kO ≤ g)
    (hoff : offOK CS OFF N = true)
    (h : ∀ j < N, repK n w GP GIP g CS OFF CI E P L K Ss SI N cap j = true)
    (hrep : ∀ i < CS.length, canonK n w (mask w) (n * w) (E (lget OFF i)) = true ∧
      siftK n w (mask w) (n * w) (pidn n w) LR TRI BP 3 0 (E (lget OFF i)) = true ∧
      ordTest n mx (arrTable n (unpack n w (E (lget OFF i)))) = true)
    (hN : (filterProducts n (ordTest n mx) (chainTables n S base) (idT n) []).length = N) :
    ∀ T ∈ filterProducts n (ordTest n mx) (chainTables n S base) (idT n) [],
      ∃ j < N, T = tabP n w (E j) := by
  obtain ⟨hb, hh, hl, hNS, hs, hp⟩ := hc
  exact CntPf.mem_records' hb hh hl hNS hs hp hgk hgp hkO hoff h hrep hN

end CFSG.KC.J2Enum

end
