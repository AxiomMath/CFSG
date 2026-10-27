module

public import CFSG.ClassicalInvolution.Q3.AE.Models
public import CFSG.Permutation.FinPack

public section

namespace CFSG.ClassicalInvolution.Q3.AE.FanoPack

open Equiv CFSG.Permutation.FinPack

@[expose] def lineF (k : Fin 7) : Finset (Fin 7) := {k, k + 1, k + 3}

theorem fanoLines_eq : fanoLines = List.ofFn lineF := by decide +kernel

theorem mem_fano {ℓ : Finset (Fin 7)} : ℓ ∈ fanoLines ↔ ∃ k, lineF k = ℓ := by
  rw [fanoLines_eq, List.mem_ofFn]

@[expose] def p1 (k : ℕ) : ℕ := Nat.mod (Nat.add k 1) 7

@[expose] def p3 (k : ℕ) : ℕ := Nat.mod (Nat.add k 3) 7

@[expose] def onL (x k : ℕ) : Bool := Nat.beq x k || Nat.beq x (p1 k) || Nat.beq x (p3 k)

theorem mem_lineF : ∀ x k : Fin 7, x ∈ lineF k ↔ onL x.val k.val = true := by decide +kernel

theorem val_p1 : ∀ k : Fin 7, (k + 1 : Fin 7).val = p1 k.val := by decide +kernel

theorem val_p3 : ∀ k : Fin 7, (k + 3 : Fin 7).val = p3 k.val := by decide +kernel

theorem card_lineF : ∀ k : Fin 7, (lineF k).card = 3 := by decide +kernel

theorem forall_lineF {k : Fin 7} {q : Fin 7 → Prop} :
    (∀ p ∈ lineF k, q p) ↔ q k ∧ q (k + 1) ∧ q (k + 3) := by
  simp only [lineF, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]

@[expose] def R7 : List ℕ := [0, 1, 2, 3, 4, 5, 6]

theorem val_mem_R7 : ∀ x : Fin 7, x.val ∈ R7 := by decide +kernel

theorem lt_of_mem_R7 {x : ℕ} (h : x ∈ R7) : x < 7 := by
  simp [R7] at h
  omega

theorem encF_rd (x k : ℕ) : encF (rd x) k = x % 16 ^ k := by
  induction k with
  | zero => simp [encF_zero, Nat.mod_one]
  | succ k ih =>
    rw [encF_succ, ih, Nat.mod_pow_succ, rd_eq]
    ring

theorem rdv (g : Perm (Fin 7)) (x : Fin 7) : (g x).val = rd (enc g) x.val :=
  (rd_enc (by norm_num) g x).symm

theorem enc_lt (g : Perm (Fin 7)) : enc g < 16 ^ 7 :=
  encF_lt fun i hi => by
    rw [dif_pos hi]
    exact lt_trans (Fin.isLt _) (by norm_num)

theorem enc7 (g : Perm (Fin 7)) : enc g = (g 0).val + (g 1).val * 16 + (g 2).val * 16 ^ 2 +
    (g 3).val * 16 ^ 3 + (g 4).val * 16 ^ 4 + (g 5).val * 16 ^ 5 + (g 6).val * 16 ^ 6 := by
  have r0 : rd (enc g) 0 = (g 0).val := rd_enc (by norm_num) g 0
  have r1 : rd (enc g) 1 = (g 1).val := rd_enc (by norm_num) g 1
  have r2 : rd (enc g) 2 = (g 2).val := rd_enc (by norm_num) g 2
  have r3 : rd (enc g) 3 = (g 3).val := rd_enc (by norm_num) g 3
  have r4 : rd (enc g) 4 = (g 4).val := rd_enc (by norm_num) g 4
  have r5 : rd (enc g) 5 = (g 5).val := rd_enc (by norm_num) g 5
  have r6 : rd (enc g) 6 = (g 6).val := rd_enc (by norm_num) g 6
  have e : enc g = encF (rd (enc g)) 7 := by rw [encF_rd, Nat.mod_eq_of_lt (enc_lt g)]
  rw [e]
  simp only [encF_succ, encF_zero, r0, r1, r2, r3, r4, r5, r6]
  ring

@[expose] def ID : ℕ := 106181136

theorem enc_one : enc (1 : Perm (Fin 7)) = ID := by
  rw [enc7]
  rfl

@[expose] def neK (c d : ℕ) : Bool := !Nat.beq c d

theorem neK_iff {c d : ℕ} : neK c d = true ↔ c ≠ d := by
  unfold neK
  constructor
  · intro h e
    subst e
    simp [Nat.beq_refl] at h
  · intro h
    cases e : Nat.beq c d
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true e) h

theorem enc_eq_iff {g h : Perm (Fin 7)} : g = h ↔ enc g = enc h :=
  ⟨fun e => e ▸ rfl, enc_inj (by norm_num)⟩

@[expose] def lo (P : ℕ) : ℕ := Nat.land P 268435455

@[expose] def hi (P : ℕ) : ℕ := Nat.shiftRight P 32

@[expose] def chk7 (f : ℕ → Bool) : Bool := f 0 && f 1 && f 2 && f 3 && f 4 && f 5 && f 6

theorem chk7_spec {f : ℕ → Bool} (h : chk7 f = true) (i : Fin 7) : f i.val = true := by
  simp only [chk7, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  fin_cases i
  exacts [h0, h1, h2, h3, h4, h5, h6]

@[expose] def okP (P : ℕ) : Bool :=
  Nat.blt (lo P) 268435456 && Nat.blt (hi P) 268435456 && chk7 fun i =>
    Nat.blt (rd (lo P) i) 7 && Nat.blt (rd (hi P) i) 7 &&
      Nat.beq (rd (hi P) (rd (lo P) i)) i && Nat.beq (rd (lo P) (rd (hi P) i)) i

theorem okP_lt {P : ℕ} (h : okP P = true) : lo P < 16 ^ 7 ∧ hi P < 16 ^ 7 := by
  simp only [okP, Bool.and_eq_true, Nat.blt_eq] at h
  exact ⟨lt_of_lt_of_eq h.1.1 (by norm_num), lt_of_lt_of_eq h.1.2 (by norm_num)⟩

theorem okP_spec {P : ℕ} (h : okP P = true) (i : Fin 7) :
    rd (lo P) i < 7 ∧ rd (hi P) i < 7 ∧ rd (hi P) (rd (lo P) i) = i ∧
      rd (lo P) (rd (hi P) i) = i := by
  simp only [okP, Bool.and_eq_true] at h
  have := chk7_spec h.2 i
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at this
  obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := this
  exact ⟨a, b, c, d⟩

@[expose] def ofPair (P : ℕ) (h : okP P = true) : Perm (Fin 7) where
  toFun i := ⟨rd (lo P) i % 7, Nat.mod_lt _ (by norm_num)⟩
  invFun i := ⟨rd (hi P) i % 7, Nat.mod_lt _ (by norm_num)⟩
  left_inv i := by
    obtain ⟨a, -, c, -⟩ := okP_spec h i
    apply Fin.ext
    dsimp only
    rw [Nat.mod_eq_of_lt a, c, Nat.mod_eq_of_lt i.isLt]
  right_inv i := by
    obtain ⟨-, b, -, d⟩ := okP_spec h i
    apply Fin.ext
    dsimp only
    rw [Nat.mod_eq_of_lt b, d, Nat.mod_eq_of_lt i.isLt]

theorem enc_ofPair {P : ℕ} (h : okP P = true) : enc (ofPair P h) = lo P := by
  have e : encF (fun i => if hi : i < 7 then ((ofPair P h ⟨i, hi⟩ : Fin 7) : ℕ) else 0) 7 =
      encF (rd (lo P)) 7 :=
    encF_congr fun i hi => by
      rw [dif_pos hi]
      exact Nat.mod_eq_of_lt (okP_spec h ⟨i, hi⟩).1
  rw [enc, e, encF_rd, Nat.mod_eq_of_lt (okP_lt h).1]

theorem enc_ofPair_inv {P : ℕ} (h : okP P = true) : enc (ofPair P h)⁻¹ = hi P := by
  have e : encF (fun i => if hi : i < 7 then (((ofPair P h)⁻¹ ⟨i, hi⟩ : Fin 7) : ℕ) else 0) 7 =
      encF (rd (hi P)) 7 :=
    encF_congr fun i hi => by
      rw [dif_pos hi]
      exact Nat.mod_eq_of_lt (okP_spec h ⟨i, hi⟩).2.1
  rw [enc, e, encF_rd, Nat.mod_eq_of_lt (okP_lt h).2]

@[expose] def L168 : List ℕ := [5177823645930582, 5724272319533142, 5983774210986582,
  6232259606745942, 9347377863341382, 9874048226051382, 10224775258711302, 10486467617031462,
  14183790243107862, 14726953235141142, 14995216926986262, 15240416641176342, 18355599336353862,
  18686548058121222, 18878984017494582, 19739888804234022, 22854749347983942, 23187888536618022,
  23386895829516342, 24245610149389062, 27360406343397702, 27889267143360822, 28236708524065062,
  28502781749043462, 72696642224198757, 73225503053714277, 73572944453833317, 73839017693679717,
  81123368058828132, 81916111678948707, 82578009109890402, 82845177566274912, 86208330196014177,
  86735000529294177, 87085727610982497, 87347419983925857, 90131525122994532, 90922078246879587,
  91588356575928672, 91848953732333922, 94630997274931812, 95209336096359522, 95424836080386147,
  95740387327746912, 99136718679191652, 99716152717157472, 99926176617742947, 100240632648565602,
  144472954575717957, 145052388614620677, 145262412512372277, 145576868546885157,
  148730126192936532, 149558045548037712, 150079239796897362, 150311232518301267,
  157736286064629252, 157984771380827712, 158769848419374642, 159316297175291427,
  162238528481469972, 163062066938463762, 163596403854358032, 163824015677654547,
  166740062234482212, 166985261867275842, 167783481572857392, 168326644645369347,
  171491949654779457, 172070288478979617, 172285788462253617, 172601339711469057,
  216828185536521237, 217406524405080597, 217622024376312597, 217937575655202837,
  221333906911159377, 221913340965052497, 222123364817462097, 222437820911018577,
  225202340969473332, 225468414226883907, 226411782335653122, 226940643150357792,
  234207405641392692, 234474574084137027, 234838508139013122, 235631251728720672,
  238715124164092212, 238976816488014147, 239923470280188192, 240450140661571842,
  243217753176105012, 243478350314693187, 243846665238307872, 244637218394694402,
  288553989087560517, 288814586194699317, 289182901165507077, 289973454337617957,
  292828684140020052, 293689588875411792, 294144812410872147, 294475761178784082,
  297328929364387092, 298187643697906962, 298651629002294547, 298984768172078352,
  301831751619465732, 302063744276910912, 302322150982177842, 303150070357184547,
  311068357947695937, 311335526421890097, 311699460492509217, 312492204097942017,
  315341249193578532, 315568860982285122, 315838219858351152, 316661758364619267,
  360677485125370437, 360905096866903077, 361174455774429957, 361997994312146997,
  364864562809471572, 365407725848376402, 365675989505819472, 365921189188870227,
  369366869634913572, 369682420932285762, 370427876914500867, 371006215769167152,
  373875876659679492, 374190332706967872, 374925931705553187, 375505365810303282,
  378692703973875777, 378924696615597057, 379183103289410337, 380011022727316017,
  387383312632717332, 387929761321726992, 388189263245624082, 388437748578779667,
  432719548608807237, 433265997296910597, 433525499218899237, 433773984555737397,
  436889102857667412, 437415773222216787, 437766500251812432, 438028192609218642,
  441725515207812417, 442268678243960097, 442536941903426817, 442782141588309297,
  445897324315628292, 446228273021669952, 446420709028221987, 447281613752062002,
  450396474355028772, 450729613496488002, 450928620805100547, 451787335093522992,
  454902131276653332, 455430992074769427, 455778433454260242, 456044506678309392]

@[expose] def TH : ℕ := 472039329825718874417530844852513919720970426439241635376

@[expose] def thK (a b : ℕ) : ℕ := rd TH (Nat.add (Nat.mul a 7) b)

@[expose] noncomputable def linesK (c : ℕ) : Bool :=
  allK (fun k => anyK (fun k' => onL (rd c k) k' && onL (rd c (p1 k)) k' &&
    onL (rd c (p3 k)) k') R7) R7

@[expose] noncomputable def okAllB : Bool :=
  allK (fun P => okP P && linesK (lo P) && linesK (hi P)) L168

theorem okAllB_eq : okAllB = true := by decide +kernel

theorem okAll {P : ℕ} (hP : P ∈ L168) : okP P = true ∧ linesK (lo P) = true ∧
    linesK (hi P) = true := by
  have := allK_iff.1 okAllB_eq P hP
  simp only [Bool.and_eq_true] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

theorem okP_of_mem {P : ℕ} (hP : P ∈ L168) : okP P = true := (okAll hP).1

@[expose] noncomputable def colB : Bool :=
  allK (fun a => allK (fun b => allK (fun x => allK (fun k =>
    !(onL a k && onL b k && onL x k) || Nat.beq a b || Nat.beq x a || Nat.beq x b ||
      Nat.beq x (thK a b)) R7) R7) R7) R7

theorem colB_eq : colB = true := by decide +kernel

theorem col_th {a b x k : ℕ} (ha : a ∈ R7) (hb : b ∈ R7) (hx : x ∈ R7) (hk : k ∈ R7)
    (h1 : onL a k = true) (h2 : onL b k = true) (h3 : onL x k = true) (hab : a ≠ b)
    (hxa : x ≠ a) (hxb : x ≠ b) : x = thK a b := by
  have := allK_iff.1 (allK_iff.1 (allK_iff.1 (allK_iff.1 colB_eq a ha) b hb) x hx) k hk
  simp only [h1, h2, h3, Bool.and_self, Bool.not_true, Bool.false_or, Bool.or_eq_true,
    Nat.beq_eq] at this
  rcases this with ((h | h) | h) | h
  · exact absurd h hab
  · exact absurd h hxa
  · exact absurd h hxb
  · exact h

theorem mem_l32_iff {c : Perm (Fin 7)} : c ∈ l32 ↔
    ∀ s ∈ fanoLines, s.map c.toEmbedding ∈ fanoLines ∧ s.map c⁻¹.toEmbedding ∈ fanoLines :=
  Iff.rfl

theorem col_img {c : Perm (Fin 7)} (hc : c ∈ l32) (k : Fin 7) :
    ∃ k' : Fin 7, c k ∈ lineF k' ∧ c (k + 1) ∈ lineF k' ∧ c (k + 3) ∈ lineF k' := by
  have h := (mem_l32_iff.1 hc (lineF k) (mem_fano.2 ⟨k, rfl⟩)).1
  obtain ⟨k', hk'⟩ := mem_fano.1 h
  refine ⟨k', ?_, ?_, ?_⟩ <;> rw [hk'] <;> exact Finset.mem_map_of_mem _ (by simp [lineF])

theorem ne_add : ∀ k : Fin 7, k ≠ k + 1 ∧ k + 3 ≠ k ∧ k + 3 ≠ k + 1 := by decide +kernel

theorem third {c : Perm (Fin 7)} (hc : c ∈ l32) (k : Fin 7) :
    (c (k + 3)).val = thK (c k).val (c (k + 1)).val := by
  obtain ⟨k', h0, h1, h3⟩ := col_img hc k
  rw [mem_lineF] at h0 h1 h3
  have inj : ∀ i j : Fin 7, i ≠ j → (c i).val ≠ (c j).val :=
    fun i j h e => h (c.injective (Fin.ext e))
  obtain ⟨n1, n2, n3⟩ := ne_add k
  exact col_th (val_mem_R7 _) (val_mem_R7 _) (val_mem_R7 _) (val_mem_R7 k') h0 h1 h3
    (inj _ _ n1) (inj _ _ n2) (inj _ _ n3)

@[expose] def codeT (a b x : ℕ) : ℕ :=
  a + b * 16 + x * 16 ^ 2 + thK a b * 16 ^ 3 + thK b x * 16 ^ 4 + thK x (thK a b) * 16 ^ 5 +
    thK (thK a b) (thK b x) * 16 ^ 6

@[expose] noncomputable def coverB : Bool :=
  allK (fun a => allK (fun b => allK (fun x => Nat.beq a b || Nat.beq a x || Nat.beq b x ||
    Nat.beq x (thK a b) || anyK (fun P => Nat.beq (lo P) (codeT a b x)) L168) R7) R7) R7

theorem coverB_eq : coverB = true := by decide +kernel

theorem cover {c : Perm (Fin 7)} (hc : c ∈ l32) : ∃ P ∈ L168, enc c = lo P := by
  have inj : ∀ i j : Fin 7, i ≠ j → (c i).val ≠ (c j).val :=
    fun i j h e => h (c.injective (Fin.ext e))
  have h3 : (c 3).val = thK (c 0).val (c 1).val := third hc 0
  have h4 : (c 4).val = thK (c 1).val (c 2).val := third hc 1
  have h5 : (c 5).val = thK (c 2).val (c 3).val := third hc 2
  have h6 : (c 6).val = thK (c 3).val (c 4).val := third hc 3
  have e : enc c = codeT (c 0).val (c 1).val (c 2).val := by
    rw [codeT, enc7, h5, h6, h3, h4]
  have := allK_iff.1 (allK_iff.1 (allK_iff.1 coverB_eq _ (val_mem_R7 (c 0))) _
    (val_mem_R7 (c 1))) _ (val_mem_R7 (c 2))
  have n01 := inj 0 1 (by decide)
  have n02 := inj 0 2 (by decide)
  have n12 := inj 1 2 (by decide)
  have n23 : (c 2).val ≠ thK (c 0).val (c 1).val := fun e => inj 2 3 (by decide) (e.trans h3.symm)
  simp only [Bool.or_eq_true, Nat.beq_eq, n01, n02, n12, n23, false_or] at this
  obtain ⟨P, hP, hc'⟩ := anyK_iff.1 this
  simp only [Nat.beq_eq] at hc'
  exact ⟨P, hP, e.trans hc'.symm⟩

theorem mem_l32 {c : Perm (Fin 7)} (hc : c ∈ l32) :
    ∃ P ∈ L168, ∃ h : okP P = true, c = ofPair P h := by
  obtain ⟨P, hP, e⟩ := cover hc
  have hok := okP_of_mem hP
  exact ⟨P, hP, hok, enc_inj (by norm_num) (e.trans (enc_ofPair hok).symm)⟩

theorem img_line (g : Perm (Fin 7)) (k : Fin 7) (hg : linesK (enc g) = true) :
    (lineF k).map g.toEmbedding ∈ fanoLines := by
  have := allK_iff.1 hg k.val (val_mem_R7 k)
  obtain ⟨k', hk', hon⟩ := anyK_iff.1 this
  simp only [Bool.and_eq_true] at hon
  obtain ⟨⟨o0, o1⟩, o3⟩ := hon
  let K' : Fin 7 := ⟨k', lt_of_mem_R7 hk'⟩
  have m : ∀ x ∈ lineF k, g x ∈ lineF K' := by
    rw [forall_lineF]
    refine ⟨?_, ?_, ?_⟩ <;> rw [mem_lineF, rdv]
    · exact o0
    · rw [val_p1]
      exact o1
    · rw [val_p3]
      exact o3
  rw [mem_fano]
  refine ⟨K', (Finset.eq_of_subset_of_card_le ?_ ?_).symm⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 hy
    exact m x hx
  · simp only [Finset.card_map, card_lineF, le_refl]

theorem lines_mem (g : Perm (Fin 7)) (hg : linesK (enc g) = true)
    (hgi : linesK (enc g⁻¹) = true) : g ∈ l32 := by
  rw [mem_l32_iff]
  intro s hs
  obtain ⟨k, rfl⟩ := mem_fano.1 hs
  exact ⟨img_line g k hg, img_line g⁻¹ k hgi⟩

theorem ofPair_mem {P : ℕ} (hP : P ∈ L168) (h : okP P = true) : ofPair P h ∈ l32 := by
  obtain ⟨-, h1, h2⟩ := okAll hP
  exact lines_mem _ (by rw [enc_ofPair]; exact h1) (by rw [enc_ofPair_inv]; exact h2)

@[expose] def fixK (c x : ℕ) : Bool := Nat.beq (rd c x) x

@[expose] def predK (i k c : ℕ) : Bool := fixK c i && fixK c k && fixK c (p1 k) && fixK c (p3 k)

theorem fix_iff (g : Perm (Fin 7)) (x : Fin 7) : g x = x ↔ fixK (enc g) x.val = true := by
  unfold fixK
  rw [Nat.beq_eq, ← rdv, Fin.ext_iff]

theorem pred_iff (g : Perm (Fin 7)) (i₀ k : Fin 7) :
    (g i₀ = i₀ ∧ ∀ p ∈ lineF k, g p = p) ↔ predK i₀.val k.val (enc g) = true := by
  rw [forall_lineF, fix_iff, fix_iff g k, fix_iff g (k + 1), fix_iff g (k + 3), val_p1, val_p3]
  simp only [predK, Bool.and_eq_true, and_assoc]

abbrev psP (i₀ : Fin 7) (ℓ : Finset (Fin 7)) (g : Perm (Fin 7)) : Prop :=
  g i₀ = i₀ ∧ (∀ p ∈ ℓ, g p = p) ∧ g ∈ l32

theorem psP_of {i₀ k : Fin 7} {P : ℕ} (hP : P ∈ L168) (h : okP P = true)
    (hp : predK i₀.val k.val (lo P) = true) : psP i₀ (lineF k) (ofPair P h) := by
  rw [← enc_ofPair h, ← pred_iff] at hp
  exact ⟨hp.1, hp.2, ofPair_mem hP h⟩

@[expose] noncomputable def flagAll (f : ℕ → ℕ → Bool) : Bool :=
  allK (fun i => allK (fun k => !onL i k || f i k) R7) R7

theorem flag_of {f : ℕ → ℕ → Bool} (h : flagAll f = true) {i₀ : Fin 7} {ℓ : Finset (Fin 7)}
    (hℓ : ℓ ∈ fanoLines) (hi : i₀ ∈ ℓ) : ∃ k : Fin 7, lineF k = ℓ ∧ f i₀.val k.val = true := by
  obtain ⟨k, rfl⟩ := mem_fano.1 hℓ
  refine ⟨k, rfl, ?_⟩
  have := allK_iff.1 (allK_iff.1 h _ (val_mem_R7 i₀)) _ (val_mem_R7 k)
  simp only [(mem_lineF i₀ k).1 hi, Bool.not_true, Bool.false_or] at this
  exact this

@[expose] noncomputable def cardB : Bool :=
  flagAll fun i k => Nat.beq (L168.filter fun P => predK i k (lo P)).length 4

theorem cardB_eq : cardB = true := by decide +kernel

theorem nodupL : (L168.map lo).Nodup := by decide +kernel

theorem card_PS (i₀ : Fin 7) (ℓ : Finset (Fin 7)) (hℓ : ℓ ∈ fanoLines) (hi : i₀ ∈ ℓ)
    (s : Finset (Perm (Fin 7))) (hs : ∀ g, g ∈ s ↔ psP i₀ ℓ g) : s.card = 4 := by
  obtain ⟨k, rfl, hf⟩ := flag_of cardB_eq hℓ hi
  rw [Nat.beq_eq] at hf
  have himg : s.image enc = ((L168.filter fun P => predK i₀.val k.val (lo P)).map lo).toFinset := by
    ext x
    simp only [Finset.mem_image, List.mem_toFinset, List.mem_map, List.mem_filter]
    constructor
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨h1, h2, h3⟩ := (hs g).1 hg
      obtain ⟨P, hP, hok, rfl⟩ := mem_l32 h3
      have := (pred_iff _ i₀ k).1 ⟨h1, h2⟩
      rw [enc_ofPair] at this ⊢
      exact ⟨P, ⟨hP, this⟩, rfl⟩
    · rintro ⟨P, ⟨hP, hpr⟩, rfl⟩
      have hok := okP_of_mem hP
      exact ⟨ofPair P hok, (hs _).2 (psP_of hP hok hpr), enc_ofPair hok⟩
  have hnd : ((L168.filter fun P => predK i₀.val k.val (lo P)).map lo).Nodup :=
    nodupL.sublist (List.filter_sublist.map lo)
  rw [← Finset.card_image_of_injective s (fun a b e => enc_inj (by norm_num) e), himg,
    List.toFinset_card_of_nodup hnd, List.length_map, hf]

@[expose] noncomputable def sqB : Bool :=
  flagAll fun i k => allK (fun P => !predK i k (lo P) || Nat.beq (mulK 7 (lo P) (lo P)) ID) L168

theorem sqB_eq : sqB = true := by decide +kernel

theorem enc_mul7 (g h : Perm (Fin 7)) : enc (g * h) = mulK 7 (enc g) (enc h) :=
  enc_mul (by norm_num) g h

theorem sq_PS (i₀ : Fin 7) (ℓ : Finset (Fin 7)) (hℓ : ℓ ∈ fanoLines) (hi : i₀ ∈ ℓ)
    (g : Perm (Fin 7)) (hg : psP i₀ ℓ g) : g * g = 1 := by
  obtain ⟨k, rfl, hf⟩ := flag_of sqB_eq hℓ hi
  obtain ⟨h1, h2, h3⟩ := hg
  obtain ⟨P, hP, hok, rfl⟩ := mem_l32 h3
  have hp := (pred_iff _ i₀ k).1 ⟨h1, h2⟩
  rw [enc_ofPair] at hp
  have := allK_iff.1 hf P hP
  simp only [hp, Bool.not_true, Bool.false_or, Nat.beq_eq] at this
  rw [enc_eq_iff, enc_mul7, enc_ofPair, this, enc_one]

@[expose] noncomputable def cubeK (c : ℕ) : ℕ := mulK 7 (mulK 7 c c) c

@[expose] noncomputable def condK (i c : ℕ) : Bool := fixK c i && Nat.beq (cubeK c) ID && neK c ID

theorem condK_of {i₀ : Fin 7} {c : Perm (Fin 7)} (h1 : c i₀ = i₀) (h2 : c * c * c = 1)
    (h3 : c ≠ 1) : condK i₀.val (enc c) = true := by
  have e2 : cubeK (enc c) = ID := by rw [cubeK, ← enc_mul7, ← enc_mul7, h2, enc_one]
  have e3 : enc c ≠ ID := fun e => h3 (by rw [enc_eq_iff, e, enc_one])
  simp only [condK, Bool.and_eq_true, (fix_iff c i₀).1 h1, e2, Nat.beq_refl, neK_iff.2 e3,
    and_self]

@[expose] noncomputable def movB : Bool :=
  flagAll fun i k => allK (fun P => !condK i (lo P) ||
    !(onL (rd (lo P) k) k && onL (rd (lo P) (p1 k)) k && onL (rd (lo P) (p3 k)) k)) L168

theorem movB_eq : movB = true := by decide +kernel

theorem moves_PS (i₀ : Fin 7) (ℓ : Finset (Fin 7)) (hℓ : ℓ ∈ fanoLines) (hi : i₀ ∈ ℓ)
    (c : Perm (Fin 7)) (h1 : c i₀ = i₀) (h2 : c * c * c = 1) (h3 : c ≠ 1) (h4 : c ∈ l32) :
    ℓ.map c.toEmbedding ≠ ℓ := by
  obtain ⟨k, rfl, hf⟩ := flag_of movB_eq hℓ hi
  have hc := condK_of h1 h2 h3
  obtain ⟨P, hP, hok, rfl⟩ := mem_l32 h4
  rw [enc_ofPair] at hc
  have := allK_iff.1 hf P hP
  simp only [hc, Bool.not_true, Bool.false_or] at this
  intro e
  have m : ∀ x ∈ lineF k, ofPair P hok x ∈ lineF k := fun x hx => by
    rw [← e]
    exact Finset.mem_map_of_mem _ hx
  rw [forall_lineF] at m
  obtain ⟨m0, m1, m3⟩ := m
  rw [mem_lineF, rdv, enc_ofPair] at m0 m1 m3
  rw [val_p1] at m1
  rw [val_p3] at m3
  simp [m0, m1, m3] at this

@[expose] noncomputable def blockK (i t : ℕ) : Bool :=
  allK (fun k => !onL i k || (onL (rd t k) k && onL (rd t (p1 k)) k && onL (rd t (p3 k)) k)) R7

theorem block_of {i₀ : Fin 7} {T : Perm (Fin 7)} (h : blockK i₀.val (enc T) = true) :
    ∀ ℓ ∈ fanoLines, i₀ ∈ ℓ → ∀ p ∈ ℓ, T p ∈ ℓ := by
  intro ℓ hℓ hi
  obtain ⟨k, rfl⟩ := mem_fano.1 hℓ
  have := allK_iff.1 h k.val (val_mem_R7 k)
  simp only [(mem_lineF i₀ k).1 hi, Bool.not_true, Bool.false_or, Bool.and_eq_true] at this
  obtain ⟨⟨o0, o1⟩, o3⟩ := this
  rw [forall_lineF]
  refine ⟨?_, ?_, ?_⟩ <;> rw [mem_lineF, rdv]
  · exact o0
  · rw [val_p1]
    exact o1
  · rw [val_p3]
    exact o3

@[expose] noncomputable def keyT (i k c ci a t : ℕ) : Bool :=
  predK i k t && (blockK i t && (neK t ID && (neK a ID && (neK a t &&
    (Nat.beq (mulK 7 a a) ID && (Nat.beq (mulK 7 t t) ID && (predK i k (mulK 7 a t) &&
    (Nat.beq (mulK 7 (mulK 7 (mulK 7 a c) a) c) ID &&
    Nat.beq (mulK 7 (mulK 7 (mulK 7 (mulK 7 c t) ci) a) (mulK 7 (mulK 7 c t) ci))
      (mulK 7 a t)))))))))

@[expose] noncomputable def keyB : Bool :=
  flagAll fun i k => allK (fun P => !condK i (lo P) ||
    anyK (fun PA => predK i k (lo PA) &&
      anyK (fun PT => keyT i k (lo P) (hi P) (lo PA) (lo PT)) L168) L168) L168

theorem keyB_eq : keyB = true := by decide +kernel

theorem key_PS (i₀ : Fin 7) (ℓ : Finset (Fin 7)) (hℓ : ℓ ∈ fanoLines) (hi : i₀ ∈ ℓ)
    (c : Perm (Fin 7)) (h1 : c i₀ = i₀) (h2 : c * c * c = 1) (h3 : c ≠ 1) (h4 : c ∈ l32) :
    ∃ A, psP i₀ ℓ A ∧ ∃ T, psP i₀ ℓ T ∧ (∀ ℓ' ∈ fanoLines, i₀ ∈ ℓ' → ∀ p ∈ ℓ', T p ∈ ℓ') ∧
      T ≠ 1 ∧ A ≠ 1 ∧ A ≠ T ∧ A * A = 1 ∧ T * T = 1 ∧ psP i₀ ℓ (A * T) ∧
      A * c * A * c = 1 ∧ (c * T * c⁻¹) * A * (c * T * c⁻¹) = A * T := by
  obtain ⟨k, rfl, hf⟩ := flag_of keyB_eq hℓ hi
  have hc := condK_of h1 h2 h3
  obtain ⟨P, hP, hok, rfl⟩ := mem_l32 h4
  rw [enc_ofPair] at hc
  have := allK_iff.1 hf P hP
  simp only [hc, Bool.not_true, Bool.false_or] at this
  obtain ⟨PA, hPA, hA⟩ := anyK_iff.1 this
  simp only [Bool.and_eq_true] at hA
  obtain ⟨hpa, hA⟩ := hA
  obtain ⟨PT, hPT, hT⟩ := anyK_iff.1 hA
  simp only [keyT, Bool.and_eq_true, neK_iff, Nat.beq_eq] at hT
  obtain ⟨hpt, hbl, n1, n2, n3, s1, s2, hpat, r1, r2⟩ := hT
  have okA := okP_of_mem hPA
  have okT := okP_of_mem hPT
  have hAT : psP i₀ (lineF k) (ofPair PA okA * ofPair PT okT) := by
    refine ⟨?_, ?_, mul_mem (ofPair_mem hPA okA) (ofPair_mem hPT okT)⟩ <;>
      rw [← enc_ofPair okA, ← enc_ofPair okT, ← enc_mul7, ← pred_iff] at hpat
    · exact hpat.1
    · exact hpat.2
  refine ⟨ofPair PA okA, psP_of hPA okA hpa, ofPair PT okT, psP_of hPT okT hpt,
    block_of (by rw [enc_ofPair]; exact hbl), ?_, ?_, ?_, ?_, ?_, hAT, ?_, ?_⟩
  all_goals simp only [ne_eq, enc_eq_iff, enc_mul7, enc_ofPair, enc_ofPair_inv, enc_one]
  exacts [n1, n2, n3, s1, s2, r1, r2]

end CFSG.ClassicalInvolution.Q3.AE.FanoPack
